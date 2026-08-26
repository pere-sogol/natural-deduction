"""Worked problems: the library the app opens with, and the test corpus.

Each entry is a sequent to prove.  Where a solution is recorded it is a
derivation built the forward way, which the tests replay to check that
the editor's model agrees with the engine, and which the app can step
through to show a proof being assembled.

Written once and used three times: as the exercises a student picks from,
as the fixtures the round-trip tests run on, and as the demonstrations.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Callable, Dict, Optional, Tuple

from nd.formula import Constant, Formula, Variable
from nd.parser import parse

from ndweb.derivation import Binding, Goal, Node, Step

__all__ = ["Exercise", "EXERCISES", "solution", "Builder"]


class Builder:
    """Allocates node ids while a derivation is written out in code."""

    def __init__(self, start: int = 1) -> None:
        self.next_id = start

    def step(self, rule: str, children=(), claim: Optional[Formula] = None,
             **params) -> Step:
        node_id = self.next_id
        self.next_id += 1
        return Step(
            node_id,
            rule,
            tuple(children),
            tuple(Binding(name, value) for name, value in params.items()),
            claim,
        )

    def assume(self, formula: Formula) -> Step:
        return self.step("Assumption", formula=formula)

    def goal(self, target: Formula) -> Goal:
        node_id = self.next_id
        self.next_id += 1
        return Goal(node_id, target)


@dataclass(frozen=True)
class Exercise:
    """One sequent to prove."""

    key: str
    title: str
    premises: Tuple[str, ...]
    goal: str
    note: str = ""

    @property
    def sequent(self) -> str:
        left = ", ".join(self.premises)
        return "{0} ⊢ {1}".format(left, self.goal) if left else "⊢ " + self.goal


EXERCISES = (
    Exercise("identity", "The conditional on itself", (), "P -> P",
             "One step: assume P, then discharge it."),
    Exercise("excluded-middle", "Excluded middle", (), "P | ~P",
             "Needs the classical rule: assume the negation of what you want."),
    Exercise("double-negation", "Double negation", (), "~~P -> P",
             "¬Elim discharges the negation of its own conclusion."),
    Exercise("modus-tollens", "Contraposition", (), "(P -> Q) -> (~Q -> ~P)",
             "Three nested assumptions, discharged in the right order."),
    Exercise("distribute", "Distributing a quantifier",
             ("Ax(Fx -> Gx)", "Ax Fx"), "Ax Gx",
             "Instantiate both premises at the same arbitrary constant."),
    Exercise("not-all-not", "Some, so not all not", ("Ex Fx",), "~Ax ~Fx",
             "∃Elim needs a parameter fresh in the conclusion."),
    Exercise("self-identity", "Everything is itself", (), "Ax x=x",
             "=Intro rests on nothing, so the ∀Intro proviso holds vacuously."),
    Exercise("leibniz", "Substituting identicals", ("a=b", "Raa"), "Rbb",
             "=Elim replaces some occurrences, so it takes two steps."),
    Exercise("de-morgan", "One of De Morgan's laws", ("~(P & Q)",), "~P | ~Q",
             "Classical: assume the negation of the goal and derive both halves."),
    Exercise("russell", "Russell's paradox", ("Ex Ay(Rxy <-> ~Ryy)",), "P",
             "The premise is contradictory, so anything follows."),
)

_BY_KEY = dict((exercise.key, exercise) for exercise in EXERCISES)


def exercise(key: str) -> Exercise:
    return _BY_KEY[key]


# -- recorded solutions ----------------------------------------------------
# Forward derivations, in the reference's subproof order.


def _identity(b: Builder) -> Node:
    p = parse("P")
    return b.step("→Intro", [b.assume(p)], assumption=p)


def _excluded_middle(b: Builder) -> Node:
    p, not_p = parse("P"), parse("~P")
    goal, denial = parse("P | ~P"), parse("~(P | ~P)")
    left = b.step("∨Intro", [b.assume(p)], conclusion=goal)
    negated = b.step("¬Intro", [left, b.assume(denial)], assumption=p)
    right = b.step("∨Intro", [negated], conclusion=goal)
    return b.step("¬Elim", [right, b.assume(denial)], conclusion=goal)


def _double_negation(b: Builder) -> Node:
    p, not_p, dn = parse("P"), parse("~P"), parse("~~P")
    inner = b.step("¬Elim", [b.assume(not_p), b.assume(dn)], conclusion=p)
    return b.step("→Intro", [inner], assumption=dn)


def _distribute(b: Builder) -> Node:
    a, x = Constant("a"), Variable("x")
    major = b.step("∀Elim", [b.assume(parse("Ax(Fx -> Gx)"))], constant=a)
    minor = b.step("∀Elim", [b.assume(parse("Ax Fx"))], constant=a)
    return b.step("∀Intro", [b.step("→Elim", [minor, major])],
                  constant=a, variable=x)


def _not_all_not(b: Builder) -> Node:
    a = Constant("a")
    denial = parse("Ax ~Fx")
    instance = b.step("∀Elim", [b.assume(denial)], constant=a)
    contradiction = b.step("¬Intro", [b.assume(parse("Fa")), instance],
                           assumption=denial)
    return b.step("∃Elim", [b.assume(parse("Ex Fx")), contradiction], constant=a)


def _self_identity(b: Builder) -> Node:
    a, x = Constant("a"), Variable("x")
    return b.step("∀Intro", [b.step("=Intro", constant=a)], constant=a, variable=x)


def _leibniz(b: Builder) -> Node:
    identity = b.assume(parse("a=b"))
    once = b.step("=Elim1", [identity, b.assume(parse("Raa"))],
                  conclusion=parse("Rba"))
    return b.step("=Elim1", [b.assume(parse("a=b")), once], conclusion=parse("Rbb"))


def _modus_tollens(b: Builder) -> Node:
    p, q = parse("P"), parse("Q")
    major, not_q = parse("P -> Q"), parse("~Q")
    reached = b.step("→Elim", [b.assume(p), b.assume(major)])
    not_p = b.step("¬Intro", [reached, b.assume(not_q)], assumption=p)
    inner = b.step("→Intro", [not_p], assumption=not_q)
    return b.step("→Intro", [inner], assumption=major)


def _de_morgan(b: Builder) -> Node:
    p, q = parse("P"), parse("Q")
    not_p, not_q = parse("~P"), parse("~Q")
    goal, denial = parse("~P | ~Q"), parse("~(~P | ~Q)")
    left = b.step("∨Intro", [b.assume(not_p)], conclusion=goal)
    got_p = b.step("¬Elim", [left, b.assume(denial)], conclusion=p)
    right = b.step("∨Intro", [b.assume(not_q)], conclusion=goal)
    got_q = b.step("¬Elim", [right, b.assume(denial)], conclusion=q)
    both = b.step("∧Intro", [got_p, got_q])
    return b.step("¬Elim", [both, b.assume(parse("~(P & Q)"))], conclusion=goal)


def _russell(b: Builder) -> Node:
    a = Constant("a")
    premise, instance = parse("Ex Ay(Rxy <-> ~Ryy)"), parse("Ay(Ray <-> ~Ryy)")
    raa, p = parse("Raa"), parse("P")

    def denial():
        """A fresh proof of ~Raa from the instance -- needed twice over."""
        biconditional = b.step("∀Elim", [b.assume(instance)], constant=a)
        forwards = b.step("↔Elim", [biconditional, b.assume(raa)])
        return b.step("¬Intro", [b.assume(raa), forwards], assumption=raa)

    biconditional = b.step("∀Elim", [b.assume(instance)], constant=a)
    got_raa = b.step("↔Elim", [biconditional, denial()])
    explosion = b.step("¬Elim", [got_raa, denial()], conclusion=p)
    return b.step("∃Elim", [b.assume(premise), explosion], constant=a)


SOLUTIONS: Dict[str, Callable[[Builder], Node]] = {
    "identity": _identity,
    "excluded-middle": _excluded_middle,
    "double-negation": _double_negation,
    "distribute": _distribute,
    "not-all-not": _not_all_not,
    "self-identity": _self_identity,
    "leibniz": _leibniz,
    "modus-tollens": _modus_tollens,
    "de-morgan": _de_morgan,
    "russell": _russell,
}


def solution(key: str, builder: Optional[Builder] = None) -> Node:
    """The recorded derivation for an exercise."""
    return SOLUTIONS[key](builder or Builder())
