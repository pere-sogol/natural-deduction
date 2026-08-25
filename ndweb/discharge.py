"""Which assumptions a step closes in each of its branches.

``Proof.discharged`` records this, but only once the step has been built,
and the editor needs it earlier: to show a student what may be assumed
inside a hole that has not been filled yet.  So it is worked out here
from the rule and its parameters alone.

That duplicates knowledge held in :mod:`nd.rules`, which is a real cost.
It is paid for by a test asserting that for every step the editor can
actually realise, this agrees exactly with the engine's own bookkeeping --
so the two cannot drift apart silently.
"""

from __future__ import annotations

from typing import Callable, Dict, FrozenSet, Optional, Tuple

from nd.formula import Formula, Not, Or

from ndweb.derivation import Node, Step, expected, kwargs

__all__ = ["discharges"]

Resolver = Callable[[Node], Optional[Formula]]


def _none(count: int) -> Tuple[FrozenSet[Formula], ...]:
    return tuple(frozenset() for _ in range(count))


def discharges(
    step: Step,
    resolve: Resolver = expected,
    values: Optional[Dict[str, object]] = None,
) -> Tuple[FrozenSet[Formula], ...]:
    """The sentences ``step`` closes in each child, in child order.

    The result is always parallel to ``step.children``, as
    ``Proof.discharged`` is to ``Proof.subproofs`` -- a step with the
    wrong number of children discharges nothing rather than guessing.

    ``resolve`` says what a child concludes.  It defaults to what the
    child merely *claims*, so contexts can be computed for a skeleton
    that has never been realised; the realiser passes one that knows the
    conclusions it has actually checked.  ``values`` overrides the step's
    own bindings for the same reason: :mod:`ndweb.unify` works out the
    parameters a half-filled block would need, and what a step discharges
    follows from those as much as from what was typed.
    """
    count = len(step.children)
    if values is None:
        values = kwargs(step)
    name = step.rule

    if name == "→Intro" and count == 1:
        assumption = values.get("assumption")
        if isinstance(assumption, Formula):
            return (frozenset({assumption}),)
        return _none(count)

    if name == "¬Intro" and count == 2:
        assumption = values.get("assumption")
        if isinstance(assumption, Formula):
            closed = frozenset({assumption})
            return (closed, closed)
        return _none(count)

    if name == "¬Elim" and count == 2:
        conclusion = values.get("conclusion")
        if isinstance(conclusion, Formula):
            closed = frozenset({Not(conclusion)})
            return (closed, closed)
        return _none(count)

    if name == "↔Intro" and count == 2:
        # pi_1 proves the right half from the left, and pi_2 the reverse,
        # so each branch discharges what the *other* one concludes.
        left, right = resolve(step.children[1]), resolve(step.children[0])
        return (
            frozenset({left}) if left is not None else frozenset(),
            frozenset({right}) if right is not None else frozenset(),
        )

    if name == "∨Elim" and count == 3:
        disjunction = resolve(step.children[2])
        if isinstance(disjunction, Or):
            return (
                frozenset({disjunction.left}),
                frozenset({disjunction.right}),
                frozenset(),
            )
        return _none(count)

    if name == "∃Elim" and count == 2:
        existential = resolve(step.children[0])
        constant = values.get("constant")
        if existential is not None and constant is not None:
            try:
                instance = existential.body.substitute(existential.variable, constant)
            except (AttributeError, TypeError):
                return _none(count)
            return (frozenset(), frozenset({instance}))
        return _none(count)

    return _none(count)
