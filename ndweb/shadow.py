"""Dressing a derivation up as something :func:`nd.render.layout` will draw.

``layout`` reads six members off each node -- ``conclusion``,
``subproofs``, ``discharged``, ``label``, ``assumptions`` and
``is_leaf`` -- and nothing else.  It never asks whether it has a
``Proof``.  So a derivation with holes still in it can be drawn by the
same code that draws finished proofs, and the drawing a student watches
grow is made by the book's own renderer rather than by a second one
written for the web that would slowly disagree with it.

A hole draws as whatever is known of it with a ``?`` beside it::

      P ^ Q  ?
    --------- ->I
    Q -> P ^ Q

An entirely blank slot draws as ``?`` alone, and rests on nothing.  What
goes in it may not have been decided yet -- on a sandbox a rule can be put
down long before there is any thought about what it will prove -- so
there is no sentence for a step below to bracket, and giving it an empty
assumption set is what keeps the renderer from inventing one.

A slot with a sentence *written* in it is different: a sentence at the top
of a step with nothing above it is assumed, so the slot rests on itself
and is bracketed when a step below discharges it.  ``ndweb.realise`` makes
that leaf a real ``Assumption``, and the assumption set drawn here is the
one the engine computed for it, so the ``[phi]`` on the page and the
``As(pi)`` the checker is working with cannot disagree.
"""

from __future__ import annotations

from typing import FrozenSet, Optional, Tuple

from nd.formula import Formula
from nd.proofs import rule

from ndweb.derivation import Goal, Node
from ndweb.discharge import discharges
from ndweb.realise import Realisation
from ndweb.unify import Solved, solve

__all__ = ["Unknown", "Shadow", "shadow"]


class Unknown:
    """Stands in for a conclusion that cannot be known yet.

    A forward step whose premises are not all there claims nothing, so
    there is no sentence to write on its line.  This prints as ``?`` and
    is equal only to itself, so it can sit where a formula would without
    ever matching one.
    """

    __slots__ = ("text",)

    def __init__(self, text: str = "?") -> None:
        self.text = text

    def __str__(self) -> str:
        return self.text

    def __repr__(self) -> str:
        return "<unknown>"

    def __eq__(self, other) -> bool:
        return self is other

    def __hash__(self) -> int:
        return id(self)


class Shadow:
    """A derivation node wearing the placement protocol."""

    def __init__(
        self,
        conclusion,
        subproofs: Tuple["Shadow", ...] = (),
        discharged: Tuple[FrozenSet[Formula], ...] = (),
        label: str = "",
        assumptions: FrozenSet[Formula] = frozenset(),
        node: Optional[Node] = None,
    ) -> None:
        self.conclusion = conclusion
        self.subproofs = subproofs
        self.discharged = discharged
        self.label = label
        self.assumptions = assumptions
        self.node = node

    @property
    def is_leaf(self) -> bool:
        return not self.subproofs


def shadow(
    node: Node,
    realisation: Optional[Realisation] = None,
    solved: Optional[Solved] = None,
) -> Shadow:
    """Build the drawable stand-in for a derivation."""
    if solved is None:
        solved = solve(node)

    def resolve(found: Node):
        return solved.formula(found.id)

    return _shadow(node, realisation, solved, resolve)


def _shadow(node: Node, realisation, solved: Solved, resolve) -> Shadow:
    if isinstance(node, Goal):
        # A blank slot rests on nothing, so no step below it may bracket
        # it as discharged.  One written into rests on itself, and the
        # engine's own assumption set for that leaf is what says so.
        known = solved.formula(node.id)
        proof = realisation.proofs.get(node.id) if realisation is not None else None
        return Shadow(
            known if known is not None else Unknown(),
            label="?",
            assumptions=proof.assumptions if proof is not None else frozenset(),
            node=node,
        )

    children = tuple(
        _shadow(child, realisation, solved, resolve) for child in node.children
    )
    closed = discharges(node, resolve, solved.params.get(node.id))
    if len(closed) != len(children):
        closed = tuple(frozenset() for _ in children)

    proof = realisation.proofs.get(node.id) if realisation is not None else None
    if proof is not None:
        conclusion = proof.conclusion
        assumptions = proof.assumptions
    else:
        known = solved.formula(node.id)
        conclusion = known if known is not None else Unknown()
        assumptions = frozenset()
        for child, group in zip(children, closed):
            assumptions |= child.assumptions - group

    label = rule(node.rule).label if node.rule else ""
    if node.is_leaf and proof is not None:
        # A leaf that rests on itself is an assumption; the renderer needs
        # that set to decide whether to bracket it.
        assumptions = proof.assumptions

    return Shadow(conclusion, children, closed, label, assumptions, node)
