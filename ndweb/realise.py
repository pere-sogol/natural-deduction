"""Projecting a derivation onto a real proof.

Every ``Proof`` this application ever holds is made here, by calling
:func:`nd.proofs.apply` through :func:`ndweb.attempt.attempt`.  Nothing
else in ``ndweb`` constructs one.  That is what lets the backward
refinement in :mod:`ndweb.refine` be a heuristic without endangering
soundness: a wrong suggestion there can send a student down a branch that
leads nowhere, but it cannot produce a proof the engine would refuse,
because the engine checks every step regardless of who proposed it.

Failure is local.  One step that does not go through leaves its own bar
red and every other branch still drawn and still checked -- without which
the editor would be unusable, since almost every keystroke breaks
something somewhere for a moment.

A slot with a sentence written in it stands as an ``Assumption`` of that
sentence.  That is what the tree calculus says a leaf is: a sentence at
the top of a step, with nothing above it, is assumed.  So a block whose
holes have all been written into is a real proof of something -- of its
conclusion, from those sentences -- and the engine says so, provisos and
all, rather than the editor guessing.  Whether it is a proof of what was
*asked* for is then one question about its assumptions, which is what
:mod:`ndweb.assumptions` answers.

A blank slot still blocks: nothing is known there, so there is nothing to
assume.  ``blank_goals`` names those, and they are the slots that must be
filled before anything can be checked at all.
"""

from __future__ import annotations

from dataclasses import dataclass, field, replace
from typing import Dict, FrozenSet, List, Optional, Tuple

from nd.formula import Formula
from nd.proofs import Proof

from ndweb.attempt import RuleFailure, attempt
from ndweb.derivation import (
    Document,
    Goal,
    Node,
    expected,
    kwargs,
    walk,
)
from ndweb.unify import Solved, solve

__all__ = ["Realisation", "realise", "contexts", "resolver"]


@dataclass(frozen=True)
class Realisation:
    """What came of trying to check a derivation.

    ``proof`` is the root's, if the whole thing went through.  ``proofs``
    holds every subtree that did, so the parts of a half-built proof that
    are already correct can be shown as correct.

    ``open_goals`` is every slot, written into or not; ``blank_goals``
    only those with nothing in them.  The difference matters because a
    written slot is an assumption and so does not stop the block being
    checked, while a blank one does.
    """

    proof: Optional[Proof] = None
    proofs: Dict[int, Proof] = field(default_factory=dict)
    failures: Dict[int, RuleFailure] = field(default_factory=dict)
    open_goals: Tuple[int, ...] = ()
    blank_goals: Tuple[int, ...] = ()

    @property
    def complete(self) -> bool:
        return self.proof is not None

    def conclusion(self, node_id: int) -> Optional[Formula]:
        proof = self.proofs.get(node_id)
        return proof.conclusion if proof is not None else None


def realise(node: Node, solved: Optional[Solved] = None) -> Realisation:
    """Check a derivation, as far as it goes.

    ``solved`` supplies the parameters a step would be applied with.  They
    are worked out rather than stored -- a ``→Intro`` whose conclusion the
    student wrote knows perfectly well what it discharges -- and the same
    reasoning that keeps contexts out of the document keeps these out of
    it too.
    """
    proofs: Dict[int, Proof] = {}
    failures: Dict[int, RuleFailure] = {}
    open_goals: List[int] = []
    if solved is None:
        solved = solve(node)
    root = _realise(node, proofs, failures, open_goals, solved)
    blank = tuple(
        found.id for found in walk(node)
        if isinstance(found, Goal) and found.target is None
    )
    return Realisation(root, proofs, failures, tuple(open_goals), blank)


def _realise(
    node: Node,
    proofs: Dict[int, Proof],
    failures: Dict[int, RuleFailure],
    open_goals: List[int],
    solved: Solved,
) -> Optional[Proof]:
    if isinstance(node, Goal):
        open_goals.append(node.id)
        if node.target is None:
            return None
        # A sentence written at the top of a step with nothing above it is
        # an assumption of that sentence.  This is not a stand-in for one:
        # it is the same reading ``unify.predict`` already takes when it
        # stands a premise slot up to run a rule forwards, and the leaf it
        # builds is an ordinary ``Assumption``, so every proviso below
        # bites on it exactly as it would on one the student wrote out.
        #
        # A slot stays a slot all the same -- it is listed in
        # ``open_goals``, and filling it with a derivation is what turns
        # the assumption into something proved.
        outcome = attempt("Assumption", (), formula=node.target)
        if outcome.failure is not None:
            failures[node.id] = replace(outcome.failure, node=node.id)
            return None
        proofs[node.id] = outcome.proof
        return outcome.proof

    below: List[Proof] = []
    for child in node.children:
        proof = _realise(child, proofs, failures, open_goals, solved)
        if proof is not None:
            below.append(proof)

    if len(below) != len(node.children):
        failures[node.id] = RuleFailure(
            "blocked",
            "waiting on the unfinished branches above",
            rule=node.rule,
            node=node.id,
        )
        return None

    values = solved.params.get(node.id)
    if values is None:
        values = kwargs(node)
    outcome = attempt(node.rule, below, **values)
    if outcome.failure is not None:
        failures[node.id] = replace(outcome.failure, node=node.id)
        return None

    proof = outcome.proof
    if node.claim is not None and proof.conclusion != node.claim:
        # The step was built to reach one sentence and now reaches another,
        # because something above it changed.  Keep the proof -- it is a
        # real proof of something -- but say so where it happened, rather
        # than letting the mismatch surface further down.
        failures[node.id] = RuleFailure(
            "drift",
            "this was built to prove {0} but now proves {1}".format(
                node.claim, proof.conclusion
            ),
            rule=node.rule,
            node=node.id,
        )
    proofs[node.id] = proof
    return proof


def resolver(realisation: Optional[Realisation] = None):
    """What a node concludes: checked if known, claimed otherwise."""

    def resolve(node: Node) -> Optional[Formula]:
        if realisation is not None:
            found = realisation.conclusion(node.id)
            if found is not None:
                return found
        return expected(node)

    return resolve


def contexts(document: Document) -> Dict[int, FrozenSet[Formula]]:
    """What may be assumed at each node, computed rather than stored.

    Storing this on a slot would go stale the moment any discharging step
    above it changed.  One pass down from the premises costs nothing and
    cannot be wrong.

    It is advisory.  A slot may perfectly well be closed by something
    resting on other assumptions: the proof still stands, and the extra
    assumption simply shows as open at the root.  Telling a student "you
    have proved this, but not from what you were given" is more use than
    refusing the step.
    """
    found: Dict[int, FrozenSet[Formula]] = {}
    base = frozenset(document.premises)
    for root in document.roots:
        found.update(solve(root, base).available)
    return found
