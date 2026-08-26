"""What a block rests on, set against what it was given to rest on.

A leaf of a proof tree is a sentence with nothing above it, and the
calculus says what that means: it is assumed.  The editor's trees have
two sorts of leaf that qualify -- an ``Assumption`` block the student put
down deliberately, and a slot they simply wrote a sentence into -- and
nothing distinguishes them logically.  Both are sentences at the top of a
step following from nothing, so both are assumptions, and this module
tracks them the same way.  ``=Intro`` is the leaf that is not one: ``a =
a`` rests on nothing, which is exactly what makes it a theorem.

An assumption stops being open when a step below closes it, and *which*
steps close *what* is :mod:`ndweb.discharge`'s answer, computed from the
rule and its parameters.  So the walk here is one descent carrying the
set of sentences discharged on the way down: a leaf is closed if its own
sentence is in that set.  That is the book's rule -- ``As(pi)`` is a set
of sentences, so discharging phi closes every leaf labelled phi in the
subtree, not one of them -- and reading it off the descent is what makes
one number able to mark several leaves.

Two things follow that the editor could not do before.

**A half-built block still says what it rests on.**  ``Proof.assumptions``
is exact and needs a finished proof; this needs only the tree, so a block
with slots still in it can be told from one that is finished but resting
on the wrong things.

**Whether the sheet is finished is a question about assumptions.**  A
block proves the sequent when it concludes the goal and every sentence it
still rests on is one of the premises.  Any other open assumption is the
work that is left, and naming it is more use than a bare "not yet":
:class:`Tally` sorts the premises from the rest, and
:attr:`Tally.settled` is the verdict.

The copy of the engine's bookkeeping this involves is kept honest the way
:mod:`ndweb.discharge`'s is -- ``tests/test_assumptions.py`` checks that
for every block the editor can realise, the open assumptions found here
are exactly ``Proof.assumptions``.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Dict, FrozenSet, List, Optional, Tuple

from nd.formula import Formula

from ndweb.derivation import (
    CONCLUSION_PARAM,
    Document,
    Goal,
    Node,
    expected,
    kwargs,
    walk,
)
from ndweb.discharge import discharges
from ndweb.unify import Solved, solve

__all__ = ["Leaf", "Rest", "Tally", "SELF_RESTING", "leaves", "rests", "tally"]

#: The leaf rules that rest on their own conclusion.
#:
#: ``Assumption`` does, and it is the only one: ``=Intro`` concludes ``a =
#: a`` from nothing at all, so a step below it has nothing to discharge and
#: a proof consisting of it alone is a theorem.  Written out rather than
#: asked of the engine because it is wanted for trees that do not realise;
#: ``tests/test_assumptions.py`` checks it against every leaf rule there
#: is, so it cannot quietly fall behind a new one.
SELF_RESTING = frozenset({"Assumption"})


@dataclass(frozen=True)
class Leaf:
    """One sentence at the top of a block, and what became of it.

    ``slot`` says it was written into a hole rather than assumed outright.
    Nothing in the logic turns on that -- both are assumptions -- but it
    is the difference between "I have not proved this yet" and "I am
    assuming this on purpose", which is worth showing.
    """

    node: int
    formula: Formula
    discharged: bool
    slot: bool


@dataclass(frozen=True)
class Rest:
    """One sentence, and every leaf of the block carrying it.

    Grouped by sentence because that is how the calculus groups it: two
    leaves labelled ``P`` are one assumption, and one discharge closes
    both.  ``nodes`` are the leaves still open, ``closed`` those a step
    below has shut, and ``slots`` is the part of ``nodes`` that is still a
    hole -- an assumption that could yet be turned into a derivation.
    """

    formula: Formula
    nodes: Tuple[int, ...] = ()
    closed: Tuple[int, ...] = ()
    premise: bool = False
    slots: Tuple[int, ...] = ()

    @property
    def open(self) -> bool:
        return bool(self.nodes)


@dataclass(frozen=True)
class Tally:
    """The whole sheet's assumptions, against the sequent's premises.

    ``premises`` runs in the sequent's own order and includes the ones
    nothing has used yet, because "you have not used P" is a hint worth
    giving.  ``extra`` is everything else still open -- the reason the
    sheet is not finished -- and ``closed`` what has been discharged
    along the way, which is the part a student is entitled to feel good
    about.
    """

    premises: Tuple[Rest, ...] = ()
    extra: Tuple[Rest, ...] = ()
    closed: Tuple[Rest, ...] = ()
    blanks: Tuple[int, ...] = ()

    @property
    def settled(self) -> bool:
        """Nothing open that was not given, and no hole left unwritten."""
        return not self.extra and not self.blanks


def leaves(root: Node, solved: Optional[Solved] = None) -> Tuple[Leaf, ...]:
    """Every sentence at the top of ``root``, in the order they are drawn.

    A leaf's own sentence is the one *written* there -- a slot's target, a
    block's claim -- and never one worked out for it.  A sentence the
    editor has merely inferred for a slot is a suggestion; nobody has
    assumed it, and the engine will not treat it as assumed either.
    """
    if solved is None:
        solved = solve(root)
    found: List[Leaf] = []
    _descend(root, frozenset(), solved, found)
    return tuple(found)


def _written(node: Node) -> Optional[Formula]:
    """The sentence written at this node, however it was written.

    A slot has a target and a step usually has a claim, but an
    ``Assumption`` may instead carry its sentence as the parameter it
    takes -- which is the same value, since :data:`CONCLUSION_PARAM` is
    exactly the parameters that end up on the line below the bar.  Reading
    both is what keeps a block written out in code counting the same as
    one built by dropping the rule on a slot.
    """
    found = expected(node)
    if found is not None or isinstance(node, Goal):
        return found
    name = CONCLUSION_PARAM.get(node.rule)
    value = None if name is None else kwargs(node).get(name)
    return value if isinstance(value, Formula) else None


def _descend(
    node: Node, closed: FrozenSet[Formula], solved: Solved, found: List[Leaf]
) -> None:
    written = _written(node)
    if isinstance(node, Goal):
        if written is not None:
            found.append(Leaf(node.id, written, written in closed, True))
        return

    if node.is_leaf:
        if node.rule in SELF_RESTING and written is not None:
            found.append(Leaf(node.id, written, written in closed, False))
        return

    def resolve(child: Node) -> Optional[Formula]:
        return solved.formula(child.id)

    groups = discharges(node, resolve, solved.params.get(node.id))
    for child, group in zip(node.children, groups):
        _descend(child, closed | group, solved, found)


def rests(
    root: Node,
    premises: FrozenSet[Formula] = frozenset(),
    solved: Optional[Solved] = None,
) -> Tuple[Rest, ...]:
    """What ``root`` rests on, one entry per distinct sentence.

    Sorted by the printed sentence, so a panel built from this does not
    reshuffle itself when an unrelated branch changes.
    """
    open_at: Dict[Formula, List[int]] = {}
    shut_at: Dict[Formula, List[int]] = {}
    slot_at: Dict[Formula, List[int]] = {}
    for leaf in leaves(root, solved):
        for table in (open_at, shut_at, slot_at):
            table.setdefault(leaf.formula, [])
        if leaf.discharged:
            shut_at[leaf.formula].append(leaf.node)
            continue
        open_at[leaf.formula].append(leaf.node)
        if leaf.slot:
            slot_at[leaf.formula].append(leaf.node)

    return tuple(
        Rest(
            formula,
            tuple(open_at[formula]),
            tuple(shut_at[formula]),
            formula in premises,
            tuple(slot_at[formula]),
        )
        for formula in sorted(open_at, key=str)
    )


def tally(
    document: Document, solved: Optional[Dict[int, Solved]] = None
) -> Tally:
    """Every assumption on the sheet, sorted by what the sequent allows.

    ``solved`` maps a card's root id to what has already been worked out
    for it.  Every keystroke redraws the whole sheet, and solving a block
    is the expensive part of that, so a caller holding the answer already
    -- :func:`ndweb.view.view` does -- says so rather than paying twice.
    """
    premises = frozenset(document.premises)
    known = solved or {}
    gathered: List[Rest] = []
    for root in document.roots:
        gathered.extend(rests(root, premises, known.get(root.id)))

    merged: Dict[Formula, Rest] = {}
    for entry in gathered:
        found = merged.get(entry.formula)
        merged[entry.formula] = entry if found is None else Rest(
            entry.formula,
            found.nodes + entry.nodes,
            found.closed + entry.closed,
            entry.premise,
            found.slots + entry.slots,
        )

    given = tuple(
        merged.get(premise, Rest(premise, premise=True))
        for premise in _unique(document.premises)
    )
    extra = tuple(
        entry for entry in _ordered(merged) if entry.open and not entry.premise
    )
    closed = tuple(
        entry for entry in _ordered(merged) if not entry.open and not entry.premise
    )
    blanks = tuple(
        node.id
        for root in document.roots
        for node in walk(root)
        if isinstance(node, Goal) and node.target is None
    )
    return Tally(given, extra, closed, blanks)


def _ordered(merged: Dict[Formula, Rest]) -> List[Rest]:
    return [merged[formula] for formula in sorted(merged, key=str)]


def _unique(formulae) -> List[Formula]:
    """The sequent's premises, in order, without repeats."""
    found: List[Formula] = []
    for formula in formulae:
        if formula not in found:
            found.append(formula)
    return found
