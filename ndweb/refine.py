"""Working backwards: from a goal to the subgoals that would establish it.

The engine runs forwards.  ``AndIntro(pi, rho)`` takes two proofs and
yields their conjunction; there is nothing in :mod:`nd` that takes a
conjunction and asks what would prove it.  Students work the other way --
you look at what you must reach and ask what would give it to you -- so
that inverse is written here.

It is a *heuristic*, and deliberately so.  Nothing in this module builds a
proof; it only proposes subgoals, which are then proved and re-checked by
:func:`nd.proofs.apply` like anything else.  A mistake here can send
somebody down a branch that leads nowhere, which is unhelpful; it cannot
make the editor accept a bad proof, which is what matters.  That is why
this lives outside ``nd`` -- the reference defines which forward steps are
legitimate, and says nothing about how to search for them, so a table of
guesses has no business sitting beside the rules it guesses about.

Three shapes of entry:

* **determined** -- the target says everything (``phi ^ psi`` splits into
  ``phi`` and ``psi``);
* **one formula wanted** -- the target leaves something open (proving
  ``phi`` by ``->Elim`` needs an antecedent nobody can recover from
  ``phi`` alone);
* **one constant wanted** -- the quantifier rules, where the choice is
  constrained by a proviso and a bad choice is worth refusing outright.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Dict, FrozenSet, List, Optional, Tuple

from nd.formula import (
    And,
    Constant,
    Equality,
    Exists,
    Forall,
    Formula,
    FormulaError,
    Iff,
    Implies,
    Not,
    Or,
    Variable,
    fresh_constant,
    fresh_variable,
)
from nd.parser import ParseError, parse, parse_term
from nd.proofs import rule_catalogue

from ndweb.derivation import Binding

__all__ = [
    "Context",
    "Field",
    "Subgoal",
    "Refinement",
    "RefineError",
    "Probe",
    "fields",
    "refine",
    "probe",
    "BACKWARD",
]


class RefineError(Exception):
    """This rule cannot be worked backwards from this goal."""

    def __init__(self, message: str) -> None:
        self.message = message
        super().__init__(message)


@dataclass(frozen=True)
class Context:
    """What is in scope where a goal sits."""

    available: FrozenSet[Formula] = frozenset()
    constants: FrozenSet[Constant] = frozenset()

    def taken(self, *extra: Formula) -> List[Constant]:
        """Every constant to keep a fresh parameter away from."""
        found = set(self.constants)
        for formula in self.available:
            found |= formula.constants()
        for formula in extra:
            if formula is not None:
                found |= formula.constants()
        return sorted(found, key=str)


@dataclass(frozen=True)
class Field:
    """Something the student must supply before the rule can be used."""

    name: str
    kind: str  # "formula" or "constant"
    description: str
    suggestions: Tuple[str, ...] = ()
    default: str = ""


@dataclass(frozen=True)
class Subgoal:
    """One hole the refinement opens, and what may be assumed inside it."""

    target: Formula
    adds: FrozenSet[Formula] = frozenset()


@dataclass(frozen=True)
class Refinement:
    subgoals: Tuple[Subgoal, ...] = ()
    params: Tuple[Binding, ...] = ()
    warnings: Tuple[str, ...] = ()


@dataclass(frozen=True)
class Probe:
    """Whether a rule is worth offering for this goal."""

    rule: str
    available: bool
    reason: str = ""
    wants: Tuple[Field, ...] = ()


#: How much the target settles, per rule.  Drives the palette's grouping.
BACKWARD = {
    "Assumption": "determined", "=Intro": "determined",
    "∧Intro": "determined", "∨Intro1": "determined", "∨Intro2": "determined",
    "→Intro": "determined", "↔Intro": "determined",
    "∧Elim1": "formula", "∧Elim2": "formula", "→Elim": "formula",
    "∨Elim": "formula", "¬Intro": "formula", "¬Elim": "formula",
    "↔Elim1": "formula", "↔Elim2": "formula", "∀Elim": "formula",
    "∃Elim": "formula", "=Elim1": "formula", "=Elim2": "formula",
    "∀Intro": "constant", "∃Intro": "constant",
}

_SHAPES = {
    "∧Intro": (And, "a conjunction"),
    "∨Intro1": (Or, "a disjunction"),
    "∨Intro2": (Or, "a disjunction"),
    "→Intro": (Implies, "a conditional"),
    "↔Intro": (Iff, "a biconditional"),
    "¬Intro": (Not, "a negation"),
    "∀Intro": (Forall, "a universally quantified sentence"),
    "∃Intro": (Exists, "an existentially quantified sentence"),
    "=Intro": (Equality, "an identity"),
}


# -- helpers ---------------------------------------------------------------


def _shaped(rule_name: str, target: Formula) -> None:
    """Refuse a rule whose conclusion cannot look like this goal."""
    expected = _SHAPES.get(rule_name)
    if expected is None:
        return
    kind, description = expected
    if not isinstance(target, kind):
        raise RefineError(
            "{0} concludes with {1}, but the goal is {2}".format(
                rule_name, description, target
            )
        )
    if rule_name == "=Intro" and target.left != target.right:
        raise RefineError(
            "=Intro only gives an identity of something with itself, not {0}"
            .format(target)
        )


def _formula(inputs: Dict[str, str], name: str, what: str) -> Formula:
    text = (inputs or {}).get(name, "")
    if not str(text).strip():
        raise RefineError("{0} is needed: {1}".format(name, what))
    if isinstance(text, Formula):
        return text
    try:
        return parse(str(text))
    except (ParseError, FormulaError) as error:
        raise RefineError(str(error))


def _constant(inputs: Dict[str, str], name: str, what: str) -> Constant:
    text = (inputs or {}).get(name, "")
    if isinstance(text, Constant):
        return text
    if not str(text).strip():
        raise RefineError("{0} is needed: {1}".format(name, what))
    try:
        term = parse_term(str(text))
    except (ParseError, FormulaError) as error:
        raise RefineError(str(error))
    if not isinstance(term, Constant):
        raise RefineError(
            "{0} must be a constant (a to t); {1} is a variable".format(name, term)
        )
    return term


def _shaped_suggestions(context: Context, kind, pick) -> Tuple[str, ...]:
    """Formulae in scope of a given shape, as text, for one-click filling."""
    found = []
    for formula in sorted(context.available, key=str):
        if isinstance(formula, kind):
            value = pick(formula)
            if value is not None and str(value) not in found:
                found.append(str(value))
    return tuple(found)


def _replace_all(formula: Formula, old: Constant, new: Constant) -> Formula:
    """``formula`` with every ``old`` turned into ``new``.

    Done through a fresh variable because the language offers constant to
    variable and variable to term, but not constant to constant.
    """
    if old == new:
        return formula
    bridge = fresh_variable(list(formula.free_variables()) + [Variable("x")])
    return formula.replace_constant(old, bridge).substitute(bridge, new)


# -- what each rule still needs -------------------------------------------


def fields(rule_name: str, target: Formula, context: Optional[Context] = None):
    """What the student must supply to use this rule on this goal."""
    context = context or Context()
    _shaped(rule_name, target)
    kind = BACKWARD.get(rule_name)
    if kind is None:
        raise RefineError("there is no rule called {0}".format(rule_name))
    if kind == "determined":
        return ()

    if rule_name in ("∧Elim1", "∧Elim2"):
        side = "right" if rule_name == "∧Elim1" else "left"
        return (Field(side, "formula",
                      "the other conjunct, which will be discarded",
                      _shaped_suggestions(context, And,
                                          lambda f: f.right if rule_name == "∧Elim1"
                                          else f.left)),)

    if rule_name == "→Elim":
        return (Field("antecedent", "formula",
                      "the sentence psi, giving psi and psi -> {0}".format(target),
                      _shaped_suggestions(
                          context, Implies,
                          lambda f: f.left if f.right == target else None)),)

    if rule_name == "∨Elim":
        return (Field("disjunction", "formula",
                      "the disjunction to argue by cases on",
                      _shaped_suggestions(context, Or, lambda f: f)),)

    if rule_name in ("¬Intro", "¬Elim"):
        return (Field("witness", "formula",
                      "a sentence psi you can derive along with its negation",
                      tuple(str(f) for f in sorted(context.available, key=str))[:6]),)

    if rule_name == "↔Elim1":
        return (Field("other", "formula", "the left half of the biconditional",
                      _shaped_suggestions(
                          context, Iff,
                          lambda f: f.left if f.right == target else None)),)

    if rule_name == "↔Elim2":
        return (Field("other", "formula", "the right half of the biconditional",
                      _shaped_suggestions(
                          context, Iff,
                          lambda f: f.right if f.left == target else None)),)

    if rule_name == "∀Elim":
        return (Field("universal", "formula",
                      "the universally quantified sentence to instantiate",
                      _shaped_suggestions(context, Forall, lambda f: f)),)

    if rule_name == "∃Elim":
        avoid = context.taken(target)
        return (
            Field("existential", "formula",
                  "the existentially quantified sentence to work from",
                  _shaped_suggestions(context, Exists, lambda f: f)),
            Field("constant", "constant",
                  "a fresh parameter standing for the thing that exists",
                  default=str(fresh_constant(avoid))),
        )

    if rule_name in ("=Elim1", "=Elim2"):
        return (
            Field("identity", "formula", "the identity to apply",
                  _shaped_suggestions(context, Equality, lambda f: f)),
            Field("source", "formula",
                  "the sentence to rewrite; leave blank for the obvious one"),
        )

    if rule_name == "∀Intro":
        avoid = context.taken(target)
        return (Field("constant", "constant",
                      "an arbitrary parameter, not occurring in the goal",
                      default=str(fresh_constant(avoid))),)

    if rule_name == "∃Intro":
        if target.variable not in target.body.free_variables():
            return ()
        suggestions = tuple(str(c) for c in sorted(target.constants(), key=str))
        return (Field("constant", "constant",
                      "the thing the goal says exists",
                      suggestions,
                      suggestions[0] if suggestions else ""),)

    return ()


# -- the table itself ------------------------------------------------------


def refine(
    rule_name: str,
    target: Formula,
    context: Optional[Context] = None,
    inputs: Optional[Dict[str, str]] = None,
) -> Refinement:
    """The subgoals that would establish ``target`` by this rule."""
    context = context or Context()
    inputs = inputs or {}
    _shaped(rule_name, target)

    if rule_name == "Assumption":
        warnings = ()
        if target not in context.available:
            warnings = (
                "{0} is not among the premises or anything discharged above, "
                "so it will stay open".format(target),
            )
        return Refinement((), (Binding("formula", target),), warnings)

    if rule_name == "=Intro":
        return Refinement((), (Binding("constant", target.left),))

    if rule_name == "∧Intro":
        return Refinement((Subgoal(target.left), Subgoal(target.right)))

    if rule_name == "∨Intro1":
        return Refinement((Subgoal(target.left),),
                          (Binding("right", target.right),))

    if rule_name == "∨Intro2":
        return Refinement((Subgoal(target.right),),
                          (Binding("left", target.left),))

    if rule_name == "→Intro":
        return Refinement(
            (Subgoal(target.right, frozenset({target.left})),),
            (Binding("assumption", target.left),),
        )

    if rule_name == "↔Intro":
        # pi_1 proves the right half from the left, and pi_2 the reverse.
        return Refinement((
            Subgoal(target.right, frozenset({target.left})),
            Subgoal(target.left, frozenset({target.right})),
        ))

    if rule_name in ("∧Elim1", "∧Elim2"):
        side = "right" if rule_name == "∧Elim1" else "left"
        other = _formula(inputs, side, "the conjunct to be discarded")
        conjunction = And(target, other) if side == "right" else And(other, target)
        return Refinement((Subgoal(conjunction),))

    if rule_name == "→Elim":
        antecedent = _formula(inputs, "antecedent", "the sentence psi")
        return Refinement((
            Subgoal(antecedent),
            Subgoal(Implies(antecedent, target)),
        ))

    if rule_name == "∨Elim":
        disjunction = _formula(inputs, "disjunction", "the disjunction")
        if not isinstance(disjunction, Or):
            raise RefineError(
                "{0} is not a disjunction, so there are no cases to argue by"
                .format(disjunction)
            )
        return Refinement((
            Subgoal(target, frozenset({disjunction.left})),
            Subgoal(target, frozenset({disjunction.right})),
            Subgoal(disjunction),
        ))

    if rule_name == "¬Intro":
        witness = _formula(inputs, "witness", "a sentence to contradict")
        closed = frozenset({target.sub})
        return Refinement(
            (Subgoal(witness, closed), Subgoal(Not(witness), closed)),
            (Binding("assumption", target.sub),),
        )

    if rule_name == "¬Elim":
        witness = _formula(inputs, "witness", "a sentence to contradict")
        closed = frozenset({Not(target)})
        return Refinement(
            (Subgoal(witness, closed), Subgoal(Not(witness), closed)),
            (Binding("conclusion", target),),
        )

    if rule_name in ("↔Elim1", "↔Elim2"):
        other = _formula(inputs, "other", "the other half of the biconditional")
        biconditional = (
            Iff(other, target) if rule_name == "↔Elim1" else Iff(target, other)
        )
        return Refinement((Subgoal(biconditional), Subgoal(other)))

    if rule_name == "∀Intro":
        variable = target.variable
        constant = _constant(inputs, "constant", "an arbitrary parameter")
        if constant in target.constants():
            # generalise() abstracts every occurrence, so a parameter
            # already in the goal would take its existing occurrences with
            # it: from Raa one reaches Ax Rxx, never Ax Rxa.
            raise RefineError(
                "{0} already occurs in {1}; generalising on it would abstract "
                "those occurrences too, giving a different sentence".format(
                    constant, target
                )
            )
        warnings = tuple(
            "{0} must stay arbitrary, but it occurs in {1}, which is open here"
            .format(constant, formula)
            for formula in sorted(context.available, key=str)
            if constant in formula.constants()
        )
        return Refinement(
            (Subgoal(target.body.substitute(variable, constant)),),
            (Binding("constant", constant), Binding("variable", variable)),
            warnings,
        )

    if rule_name == "∃Intro":
        variable = target.variable
        if variable not in target.body.free_variables():
            # Vacuous: the engine short-circuits, and naming a parameter
            # would only narrow its error message for nothing.
            return Refinement((Subgoal(target.body),),
                              (Binding("conclusion", target),))
        constant = _constant(inputs, "constant", "the thing said to exist")
        return Refinement(
            (Subgoal(target.body.substitute(variable, constant)),),
            (Binding("conclusion", target), Binding("constant", constant)),
        )

    if rule_name == "∀Elim":
        universal = _formula(inputs, "universal", "a universally quantified sentence")
        if not isinstance(universal, Forall):
            raise RefineError(
                "{0} is not universally quantified".format(universal)
            )
        constant = _instantiating(universal, target)
        if constant is None:
            raise RefineError(
                "no constant turns {0} into {1}".format(universal, target)
            )
        return Refinement((Subgoal(universal),), (Binding("constant", constant),))

    if rule_name == "∃Elim":
        existential = _formula(inputs, "existential", "an existential sentence")
        if not isinstance(existential, Exists):
            raise RefineError(
                "{0} is not existentially quantified".format(existential)
            )
        constant = _constant(inputs, "constant", "a fresh parameter")
        for where, formula in (("the existential", existential),
                               ("the goal", target)):
            if constant in formula.constants():
                raise RefineError(
                    "{0} must be fresh, but it occurs in {1}, {2}".format(
                        constant, where, formula
                    )
                )
        instance = existential.body.substitute(existential.variable, constant)
        warnings = tuple(
            "{0} must be fresh, but it occurs in {1}, which is open here"
            .format(constant, formula)
            for formula in sorted(context.available, key=str)
            if constant in formula.constants()
        )
        return Refinement(
            (Subgoal(existential), Subgoal(target, frozenset({instance}))),
            (Binding("constant", constant),),
            warnings,
        )

    if rule_name in ("=Elim1", "=Elim2"):
        identity = _formula(inputs, "identity", "an identity c1 = c2")
        if not isinstance(identity, Equality):
            raise RefineError("{0} is not an identity".format(identity))
        old, new = (
            (identity.left, identity.right)
            if rule_name == "=Elim1"
            else (identity.right, identity.left)
        )
        text = (inputs or {}).get("source", "")
        if str(text).strip():
            source = _formula(inputs, "source", "the sentence to rewrite")
        else:
            source = _replace_all(target, new, old)
        return Refinement(
            (Subgoal(identity), Subgoal(source)),
            (Binding("conclusion", target),),
        )

    raise RefineError("there is no rule called {0}".format(rule_name))


def _instantiating(universal: Forall, target: Formula) -> Optional[Constant]:
    """The constant c with ``universal.body[c/v] == target``, if there is one.

    Recovering it is a search rather than a computation, because
    substitution is many-valued backwards.  ``ExistsIntro`` in the engine
    searches in just this way, so the shape is not new.
    """
    body, variable = universal.body, universal.variable
    if variable not in body.free_variables():
        return next(iter(sorted(target.constants(), key=str)), Constant("a")) \
            if body == target else None
    candidates = sorted(target.constants() | body.constants(), key=str)
    for candidate in candidates or [Constant("a")]:
        try:
            if body.substitute(variable, candidate) == target:
                return candidate
        except FormulaError:
            continue
    return None


def probe(target: Formula, context: Optional[Context] = None) -> Tuple[Probe, ...]:
    """Which rules are worth offering for this goal, and why not otherwise.

    Shape is all that can be settled without the student's input, so a
    rule wanting a formula is reported available *with* what it wants.
    The engine still has the final say when the step is built.
    """
    context = context or Context()
    found = []
    for cls in rule_catalogue():
        try:
            wants = fields(cls.name, target, context)
        except RefineError as error:
            found.append(Probe(cls.name, False, error.message))
            continue
        reason = ""
        if not wants:
            try:
                refine(cls.name, target, context, {})
            except RefineError as error:
                found.append(Probe(cls.name, False, error.message))
                continue
        found.append(Probe(cls.name, True, reason, wants))
    return tuple(found)
