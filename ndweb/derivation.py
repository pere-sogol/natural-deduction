"""The proof under construction.

A :class:`nd.proofs.Proof` is always complete and always valid -- building
one *is* applying a rule, and an invalid one cannot exist.  That is what
makes the checker trustworthy and it is also why the editor cannot use it
as a working representation: a proof being built has holes in it, and a
hole is not a proof of anything.

So the editor owns its own tree.  A :class:`Goal` is a slot -- somewhere a
sentence will go, which may already say which sentence, or may still be
blank.  A :class:`Step` is a rule applied to children that may themselves
be slots.  :mod:`ndweb.realise` projects a hole-free derivation onto a real
``Proof`` by calling ``apply``, and that projection is the only route by
which a ``Proof`` ever comes into existence here.  Nothing in this package
builds one directly.

Three details that are easy to get wrong and are load-bearing:

**A slot may be blank.**  ``Goal.target`` is optional.  A workspace where
every hole had to announce what it would eventually contain could only be
driven backwards from a goal; the point of the sandbox is that a rule can
be put down first and filled in afterwards, in whatever order suits.

**A step remembers what it was told to conclude.**  ``Step.claim`` is the
sentence written on the line below the bar when the student wrote one
there.  Where the premises settle the conclusion it is redundant and is
checked against them; where they do not -- ``∨Intro`` may add any disjunct
at all -- it is the only thing that says which conclusion was meant.

**A slot does not store what may be assumed at it.**  That depends on
every discharging step above it, so storing it would go stale the moment
any of them changed.  :func:`ndweb.realise.contexts` computes it instead.
"""

from __future__ import annotations

from dataclasses import dataclass, replace
from typing import Dict, Iterator, List, Optional, Tuple, Union

from nd.formula import Formula
from nd.proofs import rule

__all__ = [
    "Binding",
    "Goal",
    "Step",
    "Card",
    "Document",
    "Node",
    "CONCLUSION_PARAM",
    "walk",
    "find",
    "card_of",
    "substitute_node",
    "detach_node",
    "expected",
    "kwargs",
    "arity",
    "parameters",
]

#: Rules where one parameter simply *is* the conclusion.
#:
#: ``∃Intro`` is told the existential it claims, ``¬Elim`` the sentence it
#: concludes, ``=Elim`` the rewritten sentence, ``Assumption`` what is
#: assumed -- and in every case that value also ends up written on the line
#: below the bar.  Making the student type it in two places would invite
#: the two to disagree, so the conclusion slot fills the parameter and the
#: parameter is not offered separately.
CONCLUSION_PARAM = {
    "Assumption": "formula",
    "¬Elim": "conclusion",
    "∃Intro": "conclusion",
    "=Elim1": "conclusion",
    "=Elim2": "conclusion",
}


@dataclass(frozen=True)
class Binding:
    """One of a rule's declared parameters, ready to be applied.

    ``name`` is exactly ``nd.proofs.Parameter.name``, which is exactly the
    constructor's keyword, so bindings splat straight into ``apply``.
    """

    name: str
    value: object  # Formula, Constant or Variable


@dataclass(frozen=True)
class Goal:
    """A slot: somewhere a sentence goes, named or not yet."""

    id: int
    target: Optional[Formula] = None

    @property
    def is_blank(self) -> bool:
        return self.target is None


@dataclass(frozen=True)
class Step:
    """A rule applied to children, which may still be slots."""

    id: int
    rule: str
    children: Tuple["Node", ...] = ()
    params: Tuple[Binding, ...] = ()
    claim: Optional[Formula] = None

    @property
    def is_leaf(self) -> bool:
        return not self.children

    def bound(self, name: str):
        for binding in self.params:
            if binding.name == name:
                return binding.value
        return None


Node = Union[Goal, Step]


@dataclass(frozen=True)
class Card:
    """A tree of the workspace, and where on the sheet it sits.

    Position is the editor's, not the logic's: it changes nothing about
    what is proved.  It is kept in the document all the same, because a
    board whose pieces jump about whenever anything is checked is not a
    board anybody can think on.
    """

    node: Node
    x: int = 40
    y: int = 40


@dataclass(frozen=True)
class Document:
    """A whole sheet: loose blocks, and optionally something to prove.

    There is no privileged tree.  Every block is the same sort of thing
    wherever it sits, and one becomes the answer by concluding the goal
    from the premises -- which is checked, not arranged for.  ``goal`` and
    ``premises`` are the exercise, and both may be absent: an empty sheet
    is a legitimate place to work.
    """

    goal: Optional[Formula] = None
    premises: Tuple[Formula, ...] = ()
    cards: Tuple[Card, ...] = ()
    next_id: int = 0

    @property
    def roots(self) -> Tuple[Node, ...]:
        return tuple(card.node for card in self.cards)

    def fresh(self) -> Tuple[int, "Document"]:
        """An unused node id, and the document that has spent it."""
        return self.next_id, replace(self, next_id=self.next_id + 1)

    def spend(self, count: int) -> Tuple[List[int], "Document"]:
        """``count`` unused ids at once."""
        ids = list(range(self.next_id, self.next_id + count))
        return ids, replace(self, next_id=self.next_id + count)


def walk(node: Node) -> Iterator[Node]:
    """Every node of this subtree, children before their parent."""
    if isinstance(node, Step):
        for child in node.children:
            for found in walk(child):
                yield found
    yield node


def find(document: Document, node_id: int) -> Optional[Node]:
    """The node with this id, wherever on the sheet it sits."""
    for root in document.roots:
        for node in walk(root):
            if node.id == node_id:
                return node
    return None


def card_of(document: Document, node_id: int) -> Optional[Card]:
    """The card whose tree contains this node."""
    for card in document.cards:
        for node in walk(card.node):
            if node.id == node_id:
                return card
    return None


def substitute_node(node: Node, node_id: int, replacement: Node) -> Node:
    """``node`` with the subtree at ``node_id`` swapped out.

    Structural, so every untouched branch is shared with the original --
    which is what lets the realisation cache survive an edit elsewhere.
    """
    if node.id == node_id:
        return replacement
    if isinstance(node, Step):
        children = tuple(
            substitute_node(child, node_id, replacement) for child in node.children
        )
        if children != node.children:
            return replace(node, children=children)
    return node


def detach_node(
    node: Node, node_id: int, leave: Optional[Formula] = None
) -> Tuple[Node, Optional[Node]]:
    """``node`` with the subtree at ``node_id`` lifted out, and that subtree.

    What is left behind is a slot naming the sentence the subtree was
    supplying, so that pulling a branch off does not also lose the record
    of what belonged there.  ``leave`` says what that sentence was; without
    it only what the subtree *claimed* is available, which for a block
    built upwards from its premises is nothing.
    """
    found = None
    for candidate in walk(node):
        if candidate.id == node_id:
            found = candidate
            break
    if found is None or found is node:
        return node, None
    left = Goal(found.id, leave if leave is not None else expected(found))
    return substitute_node(node, node_id, left), found


def expected(node: Node) -> Optional[Formula]:
    """What this node says it concludes, before anything is checked.

    A slot is its target; a step is its claim, if it was given one.
    ``None`` means the answer depends on the subtree, or on nothing at all
    yet.
    """
    if isinstance(node, Goal):
        return node.target
    return node.claim


def kwargs(step: Step) -> Dict[str, object]:
    """A step's bindings as the keywords ``apply`` wants.

    A rule listed in :data:`CONCLUSION_PARAM` takes its conclusion from
    ``claim`` unless a binding says otherwise, which is what keeps the
    sentence on the line and the value the rule was given from ever being
    two different things.
    """
    found = dict((binding.name, binding.value) for binding in step.params)
    name = CONCLUSION_PARAM.get(step.rule)
    if name is not None and found.get(name) is None and step.claim is not None:
        found[name] = step.claim
    return dict((key, value) for key, value in found.items() if value is not None)


def arity(rule_name: str) -> int:
    """How many subproofs the named rule takes."""
    return rule(rule_name).subproof_count


def parameters(rule_name: str) -> Tuple:
    """The parameters the student must supply, conclusion aside.

    The one that *is* the conclusion is filtered out: it has a slot of its
    own on the block already.
    """
    hidden = CONCLUSION_PARAM.get(rule_name)
    return tuple(p for p in rule(rule_name).parameters if p.name != hidden)
