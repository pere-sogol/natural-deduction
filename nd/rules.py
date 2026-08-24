"""The inference rules of ND, ND_2 and ND_=.

One class per rule, each a subclass of :class:`nd.proofs.Proof`: applying a
rule *is* building the node, so ``AndIntro(p, q)`` is at once the step and
the proof it yields.  Every constructor checks that the rule applies and
raises otherwise, so a proof object is always a proof.

Constructor arguments follow the reference's numbering of the subproofs,
pi_1 then pi_2 then pi_3, so each rule can be read straight off the
diagram.  That is worth knowing for two rules where the order surprises:
``<->Intro`` takes the proof of the *right* half first, and ``vElim``
takes the two case proofs before the disjunction they run on.

Arguments a rule cannot recover from its subproofs are passed explicitly
and declared in ``parameters``: which disjunct ``vIntro`` adds, which
assumption ``->Intro`` discharges, which existential ``EIntro`` claims.

Two rules verify a proposed conclusion instead of computing one.  ``EIntro``
and ``=Elim`` replace *some* occurrences, not all -- from ``Raa`` one may
infer ``Ex Rxa`` as well as ``Ex Rxx`` -- so there is nothing for them to
compute.  The caller supplies the conclusion and the rule checks it.
"""

from __future__ import annotations

from typing import Optional

from nd.formula import (
    And,
    Atom,
    CaptureError,
    Constant,
    Equality,
    Exists,
    Forall,
    Formula,
    Iff,
    Implies,
    Not,
    Or,
    Term,
    Variable,
)
from nd.proofs import (
    MismatchError,
    Parameter,
    Proof,
    ProvisoError,
    ShapeError,
    _check_constant,
    _check_formula,
    _check_subproof,
    _check_variable,
    register,
)

__all__ = [
    "Assumption",
    "EqualityIntro",
    "AndIntro",
    "AndElim1",
    "AndElim2",
    "OrIntro1",
    "OrIntro2",
    "OrElim",
    "ImpliesIntro",
    "ImpliesElim",
    "NotIntro",
    "NotElim",
    "IffIntro",
    "IffElim1",
    "IffElim2",
    "ForallIntro",
    "ForallElim",
    "ExistsIntro",
    "ExistsElim",
    "EqualityElim1",
    "EqualityElim2",
]


# --------------------------------------------------------------------------
# Shared checks
# --------------------------------------------------------------------------

_DESCRIPTIONS = {
    And: "a conjunction",
    Or: "a disjunction",
    Implies: "a conditional",
    Iff: "a biconditional",
    Not: "a negation",
    Forall: "a universally quantified sentence",
    Exists: "an existentially quantified sentence",
    Equality: "an identity",
}


def _concluding(proof: Proof, kind: type, rule_name: str, position: str) -> Formula:
    """The conclusion of ``proof``, required to have ``kind`` as its shape."""
    _check_subproof(proof, rule_name, position)
    conclusion = proof.conclusion
    if not isinstance(conclusion, kind):
        raise ShapeError(
            rule_name,
            "{0} must conclude with {1}, but it concludes {2}".format(
                position, _DESCRIPTIONS[kind], conclusion
            ),
        )
    return conclusion


def _contradictory(pi1: Proof, pi2: Proof, rule_name: str) -> None:
    """Require that the two subproofs conclude with psi and ~psi.

    There is no absurdity sign in this system: a contradictory pair is
    what the negation rules act on directly.
    """
    _check_subproof(pi1, rule_name, "pi_1")
    _check_subproof(pi2, rule_name, "pi_2")
    if pi2.conclusion != Not(pi1.conclusion):
        raise MismatchError(
            rule_name,
            "pi_1 and pi_2 must be a contradictory pair psi and its negation, "
            "but they conclude {0} and {1}".format(pi1.conclusion, pi2.conclusion),
        )


def _term_matches(source: Term, target: Term, old: Term, new: Term) -> bool:
    return source == target or (source == old and target == new)


def _replaces_some(source: Formula, target: Formula, old: Term, new: Term) -> bool:
    """True if ``target`` is ``source`` with some occurrences of ``old`` replaced.

    The identity rules licence replacing *some* occurrences, not all: from
    ``a=b`` and ``Raa`` one may infer ``Rab``, ``Rba`` or ``Rbb``.  So there
    is no formula to compute, only a proposal to check, and the check is a
    walk down both formulae in step.

    Deliberately not a method on ``Formula``: partial replacement is a
    fact about this rule, and putting it in the language layer would invite
    its use where only total replacement is sound.  Replacing nothing
    counts, since the premise itself is always a legitimate conclusion.
    """
    if isinstance(source, Atom):
        return (
            isinstance(target, Atom)
            and target.predicate == source.predicate
            and len(target.terms) == len(source.terms)
            and all(
                _term_matches(s, t, old, new)
                for s, t in zip(source.terms, target.terms)
            )
        )
    if isinstance(source, Equality):
        return (
            isinstance(target, Equality)
            and _term_matches(source.left, target.left, old, new)
            and _term_matches(source.right, target.right, old, new)
        )
    if isinstance(source, Not):
        return isinstance(target, Not) and _replaces_some(
            source.sub, target.sub, old, new
        )
    if isinstance(source, (And, Or, Implies, Iff)):
        return (
            target.__class__ is source.__class__
            and _replaces_some(source.left, target.left, old, new)
            and _replaces_some(source.right, target.right, old, new)
        )
    if isinstance(source, (Forall, Exists)):
        return (
            target.__class__ is source.__class__
            and target.variable == source.variable
            and _replaces_some(source.body, target.body, old, new)
        )
    return False


# --------------------------------------------------------------------------
# The base cases: proofs consisting of a single node
# --------------------------------------------------------------------------


@register
class Assumption(Proof):
    """(Assumption) A single node labelled phi, resting on phi itself.

    ``As(pi) = {phi}``.  Every proof is grown from these; the rules that
    discharge decide which of them the conclusion still depends on.
    """

    __slots__ = ()

    name = "Assumption"
    label = ""
    subproof_count = 0
    parameters = (Parameter("formula", "formula", "the sentence assumed"),)

    def __init__(self, formula: Formula) -> None:
        _check_formula(formula, self.name, "the sentence assumed")
        self._seal(formula, assumptions=frozenset({formula}))


@register
class EqualityIntro(Proof):
    """(=Intro) A single node labelled ``c=c``, resting on nothing.

    ``As(pi) = {}``.  The one leaf that is not an assumption, which is why
    ``|- Ax x=x`` is provable: introduce ``a=a`` and generalise, the
    proviso on ``AIntro`` holding vacuously.
    """

    __slots__ = ()

    name = "=Intro"
    label = "=I"
    subproof_count = 0
    parameters = (
        Parameter("constant", "constant", "the constant c, giving the line c=c"),
    )

    def __init__(self, constant: Constant) -> None:
        _check_constant(constant, self.name, "the constant")
        self._seal(Equality(constant, constant), assumptions=frozenset())


# --------------------------------------------------------------------------
# Conjunction
# --------------------------------------------------------------------------


@register
class AndIntro(Proof):
    """(^Intro) From phi_1 and phi_2 infer phi_1 ^ phi_2."""

    __slots__ = ()

    name = "∧Intro"
    label = "∧I"
    subproof_count = 2

    def __init__(self, pi1: Proof, pi2: Proof) -> None:
        _check_subproof(pi1, self.name, "pi_1")
        _check_subproof(pi2, self.name, "pi_2")
        self._seal(And(pi1.conclusion, pi2.conclusion), (pi1, pi2))


@register
class AndElim1(Proof):
    """(^Elim1) From phi_1 ^ phi_2 infer phi_1."""

    __slots__ = ()

    name = "∧Elim1"
    label = "∧E"
    subproof_count = 1

    def __init__(self, pi1: Proof) -> None:
        conjunction = _concluding(pi1, And, self.name, "pi_1")
        self._seal(conjunction.left, (pi1,))


@register
class AndElim2(Proof):
    """(^Elim2) From phi_1 ^ phi_2 infer phi_2."""

    __slots__ = ()

    name = "∧Elim2"
    label = "∧E"
    subproof_count = 1

    def __init__(self, pi1: Proof) -> None:
        conjunction = _concluding(pi1, And, self.name, "pi_1")
        self._seal(conjunction.right, (pi1,))


# --------------------------------------------------------------------------
# Disjunction
# --------------------------------------------------------------------------


@register
class OrIntro1(Proof):
    """(vIntro1) From phi_1 infer phi_1 v phi_2.

    The disjunct added is not determined by the premise, so it is given.
    """

    __slots__ = ()

    name = "∨Intro1"
    label = "∨I"
    subproof_count = 1
    parameters = (Parameter("right", "formula", "the disjunct added on the right"),)

    def __init__(self, pi1: Proof, right: Formula) -> None:
        _check_subproof(pi1, self.name, "pi_1")
        _check_formula(right, self.name, "the disjunct added")
        self._seal(Or(pi1.conclusion, right), (pi1,))


@register
class OrIntro2(Proof):
    """(vIntro2) From phi_2 infer phi_1 v phi_2."""

    __slots__ = ()

    name = "∨Intro2"
    label = "∨I"
    subproof_count = 1
    parameters = (Parameter("left", "formula", "the disjunct added on the left"),)

    def __init__(self, pi1: Proof, left: Formula) -> None:
        _check_subproof(pi1, self.name, "pi_1")
        _check_formula(left, self.name, "the disjunct added")
        self._seal(Or(left, pi1.conclusion), (pi1,))


@register
class OrElim(Proof):
    """(vElim) Proof by cases.

    ``pi_1`` proves phi from psi_1, ``pi_2`` proves phi from psi_2, and
    ``pi_3`` proves psi_1 v psi_2; the disjuncts are discharged from the
    case proofs that assumed them.  The subproof order is the reference's:
    the disjunction comes last.
    """

    __slots__ = ()

    name = "∨Elim"
    label = "∨E"
    subproof_count = 3

    def __init__(self, pi1: Proof, pi2: Proof, pi3: Proof) -> None:
        _check_subproof(pi1, self.name, "pi_1")
        _check_subproof(pi2, self.name, "pi_2")
        disjunction = _concluding(pi3, Or, self.name, "pi_3")
        if pi1.conclusion != pi2.conclusion:
            raise MismatchError(
                self.name,
                "both cases must reach the same conclusion, but pi_1 reaches "
                "{0} and pi_2 reaches {1}".format(pi1.conclusion, pi2.conclusion),
            )
        self._seal(
            pi1.conclusion,
            (pi1, pi2, pi3),
            (
                frozenset({disjunction.left}),
                frozenset({disjunction.right}),
                frozenset(),
            ),
        )


# --------------------------------------------------------------------------
# The conditional
# --------------------------------------------------------------------------


@register
class ImpliesIntro(Proof):
    """(->Intro) From a proof of phi, discharging psi, infer psi -> phi.

    The assumption discharged is given rather than guessed: it need not
    occur in the subproof at all, and ``psi -> phi`` follows either way.
    """

    __slots__ = ()

    name = "→Intro"
    label = "→I"
    subproof_count = 1
    parameters = (
        Parameter("assumption", "formula", "the antecedent psi, discharged from pi_1"),
    )

    def __init__(self, pi1: Proof, assumption: Formula) -> None:
        _check_subproof(pi1, self.name, "pi_1")
        _check_formula(assumption, self.name, "the assumption discharged")
        self._seal(
            Implies(assumption, pi1.conclusion), (pi1,), (frozenset({assumption}),)
        )


@register
class ImpliesElim(Proof):
    """(->Elim) From psi and psi -> phi infer phi."""

    __slots__ = ()

    name = "→Elim"
    label = "→E"
    subproof_count = 2

    def __init__(self, pi1: Proof, pi2: Proof) -> None:
        _check_subproof(pi1, self.name, "pi_1")
        conditional = _concluding(pi2, Implies, self.name, "pi_2")
        if conditional.left != pi1.conclusion:
            raise MismatchError(
                self.name,
                "the antecedent of {0} is {1}, but pi_1 concludes {2}".format(
                    conditional, conditional.left, pi1.conclusion
                ),
            )
        self._seal(conditional.right, (pi1, pi2))


# --------------------------------------------------------------------------
# Negation
# --------------------------------------------------------------------------


@register
class NotIntro(Proof):
    """(~Intro) From a contradictory pair, discharging phi, infer ~phi.

    There is no absurdity sign: the two subproofs conclude with psi and
    ~psi, and the negation of the discharged assumption is read off
    directly.
    """

    __slots__ = ()

    name = "¬Intro"
    label = "¬I"
    subproof_count = 2
    parameters = (
        Parameter(
            "assumption",
            "formula",
            "the sentence phi discharged from both subproofs; the conclusion is ~phi",
        ),
    )

    def __init__(self, pi1: Proof, pi2: Proof, assumption: Formula) -> None:
        _contradictory(pi1, pi2, self.name)
        _check_formula(assumption, self.name, "the assumption discharged")
        closed = frozenset({assumption})
        self._seal(Not(assumption), (pi1, pi2), (closed, closed))


@register
class NotElim(Proof):
    """(~Elim) From a contradictory pair, discharging ~phi, infer phi.

    The classical rule: what is discharged is the *negation* of the
    conclusion, which is how reductio and excluded middle are reached.
    """

    __slots__ = ()

    name = "¬Elim"
    label = "¬E"
    subproof_count = 2
    parameters = (
        Parameter(
            "conclusion",
            "formula",
            "the sentence phi concluded; ~phi is discharged from both subproofs",
        ),
    )

    def __init__(self, pi1: Proof, pi2: Proof, conclusion: Formula) -> None:
        _contradictory(pi1, pi2, self.name)
        _check_formula(conclusion, self.name, "the conclusion")
        closed = frozenset({Not(conclusion)})
        self._seal(conclusion, (pi1, pi2), (closed, closed))


# --------------------------------------------------------------------------
# The biconditional
# --------------------------------------------------------------------------


@register
class IffIntro(Proof):
    """(<->Intro) From each half proved from the other, infer phi_1 <-> phi_2.

    Note the order, which is the reference's: ``pi_1`` proves the *right*
    half phi_2 from phi_1, and ``pi_2`` proves the left half phi_1 from
    phi_2.  Nothing needs to be supplied -- both halves are read off the
    two conclusions.
    """

    __slots__ = ()

    name = "↔Intro"
    label = "↔I"
    subproof_count = 2

    def __init__(self, pi1: Proof, pi2: Proof) -> None:
        _check_subproof(pi1, self.name, "pi_1")
        _check_subproof(pi2, self.name, "pi_2")
        left, right = pi2.conclusion, pi1.conclusion
        self._seal(
            Iff(left, right),
            (pi1, pi2),
            (frozenset({left}), frozenset({right})),
        )


@register
class IffElim1(Proof):
    """(<->Elim1) From phi_1 <-> phi_2 and phi_1 infer phi_2."""

    __slots__ = ()

    name = "↔Elim1"
    label = "↔E"
    subproof_count = 2

    def __init__(self, pi1: Proof, pi2: Proof) -> None:
        biconditional = _concluding(pi1, Iff, self.name, "pi_1")
        _check_subproof(pi2, self.name, "pi_2")
        if biconditional.left != pi2.conclusion:
            raise MismatchError(
                self.name,
                "the left half of {0} is {1}, but pi_2 concludes {2}".format(
                    biconditional, biconditional.left, pi2.conclusion
                ),
            )
        self._seal(biconditional.right, (pi1, pi2))


@register
class IffElim2(Proof):
    """(<->Elim2) From phi_1 <-> phi_2 and phi_2 infer phi_1."""

    __slots__ = ()

    name = "↔Elim2"
    label = "↔E"
    subproof_count = 2

    def __init__(self, pi1: Proof, pi2: Proof) -> None:
        biconditional = _concluding(pi1, Iff, self.name, "pi_1")
        _check_subproof(pi2, self.name, "pi_2")
        if biconditional.right != pi2.conclusion:
            raise MismatchError(
                self.name,
                "the right half of {0} is {1}, but pi_2 concludes {2}".format(
                    biconditional, biconditional.right, pi2.conclusion
                ),
            )
        self._seal(biconditional.left, (pi1, pi2))


# --------------------------------------------------------------------------
# The quantifiers
# --------------------------------------------------------------------------


@register
class ForallIntro(Proof):
    """(AIntro) From phi[c/v], with c arbitrary, infer Av phi.

    ``c`` is arbitrary when it occurs neither in the conclusion nor in any
    assumption the subproof still rests on.  Abstraction is total -- every
    occurrence of ``c`` becomes ``v`` -- which is what makes the first half
    of that proviso hold automatically; the live condition is the second,
    and the error names the assumption that violates it.
    """

    __slots__ = ()

    name = "∀Intro"
    label = "∀I"
    subproof_count = 1
    parameters = (
        Parameter("constant", "constant", "the parameter c abstracted on"),
        Parameter("variable", "variable", "the variable v bound in the result"),
    )

    def __init__(self, pi1: Proof, constant: Constant, variable: Variable) -> None:
        _check_subproof(pi1, self.name, "pi_1")
        _check_constant(constant, self.name, "the parameter")
        _check_variable(variable, self.name, "the variable bound")
        for assumption in sorted(pi1.assumptions, key=str):
            if constant in assumption.constants():
                raise ProvisoError(
                    self.name,
                    "{0} is not arbitrary: it occurs in the undischarged "
                    "assumption {1}".format(constant, assumption),
                )
        try:
            conclusion = pi1.conclusion.generalise(constant, variable)
        except CaptureError as error:
            raise ProvisoError(self.name, str(error)) from error
        self._seal(conclusion, (pi1,))


@register
class ForallElim(Proof):
    """(AElim) From Av phi infer phi[c/v], for any constant c."""

    __slots__ = ()

    name = "∀Elim"
    label = "∀E"
    subproof_count = 1
    parameters = (
        Parameter("constant", "constant", "the constant c instantiated at"),
    )

    def __init__(self, pi1: Proof, constant: Constant) -> None:
        universal = _concluding(pi1, Forall, self.name, "pi_1")
        _check_constant(constant, self.name, "the constant instantiated at")
        # A constant has no free variables, so nothing can be captured and
        # substitute() cannot raise here.
        self._seal(universal.body.substitute(universal.variable, constant), (pi1,))


@register
class ExistsIntro(Proof):
    """(EIntro) From phi[c/v] infer Ev phi.

    The existential is supplied and checked rather than computed, because
    the rule replaces *some* occurrences: ``Raa`` yields ``Ex Rxa``,
    ``Ex Rax`` and ``Ex Rxx`` alike, and nothing in the premise says which
    was meant.  Naming ``constant`` narrows the search to one candidate
    and sharpens the message when it fails.
    """

    __slots__ = ()

    name = "∃Intro"
    label = "∃I"
    subproof_count = 1
    parameters = (
        Parameter("conclusion", "formula", "the existential Ev phi claimed"),
        Parameter(
            "constant",
            "constant",
            "the parameter c, if it should be pinned down rather than searched for",
            required=False,
        ),
    )

    def __init__(
        self,
        pi1: Proof,
        conclusion: Formula,
        constant: Optional[Constant] = None,
    ) -> None:
        _check_subproof(pi1, self.name, "pi_1")
        _check_formula(conclusion, self.name, "the conclusion")
        if not isinstance(conclusion, Exists):
            raise ShapeError(
                self.name,
                "the conclusion must be an existentially quantified sentence, "
                "not {0}".format(conclusion),
            )
        if constant is not None:
            _check_constant(constant, self.name, "the parameter")

        premise = pi1.conclusion
        body, variable = conclusion.body, conclusion.variable

        if variable not in body.free_variables():
            # Vacuous quantification: no parameter is involved at all.
            if body != premise:
                raise MismatchError(
                    self.name,
                    "{0} binds nothing, so pi_1 would have to conclude {1}, "
                    "but it concludes {2}".format(conclusion, body, premise),
                )
        else:
            candidates = (
                (constant,)
                if constant is not None
                else tuple(sorted(premise.constants(), key=str))
            )
            if not any(body.substitute(variable, c) == premise for c in candidates):
                if constant is not None:
                    raise MismatchError(
                        self.name,
                        "putting {0} for {1} in {2} gives {3}, but pi_1 concludes "
                        "{4}".format(
                            constant,
                            variable,
                            body,
                            body.substitute(variable, constant),
                            premise,
                        ),
                    )
                raise MismatchError(
                    self.name,
                    "pi_1 concludes {0}, which is not {1} with a constant put "
                    "for {2}".format(premise, body, variable),
                )
        self._seal(conclusion, (pi1,))


@register
class ExistsElim(Proof):
    """(EElim) From Ev phi and a proof of psi from phi[c/v], infer psi.

    ``c`` must be a fresh parameter: absent from the existential, from the
    conclusion, and from every assumption ``pi_2`` still rests on besides
    the instance being discharged.

    The middle condition is not stated in ``reference/NDrules.pdf`` (p.45),
    which lists only the other two.  Without it the rule is unsound: take
    ``pi_2`` to be the bare assumption ``Fa``, so that ``As(pi_2)`` minus
    the instance is empty and both stated conditions hold vacuously, and
    ``Ex Fx |- Fa`` goes through.  TLM states the proviso with psi
    included, and that is what is enforced here.
    """

    __slots__ = ()

    name = "∃Elim"
    label = "∃E"
    subproof_count = 2
    parameters = (
        Parameter(
            "constant",
            "constant",
            "the fresh parameter c; phi[c/v] is discharged from pi_2",
        ),
    )

    def __init__(self, pi1: Proof, pi2: Proof, constant: Constant) -> None:
        existential = _concluding(pi1, Exists, self.name, "pi_1")
        _check_subproof(pi2, self.name, "pi_2")
        _check_constant(constant, self.name, "the parameter")

        if constant in existential.constants():
            raise ProvisoError(
                self.name,
                "{0} is not fresh: it occurs in {1}".format(constant, existential),
            )
        if constant in pi2.conclusion.constants():
            raise ProvisoError(
                self.name,
                "{0} is not fresh: it occurs in the conclusion {1}".format(
                    constant, pi2.conclusion
                ),
            )
        instance = existential.body.substitute(existential.variable, constant)
        for assumption in sorted(pi2.assumptions - {instance}, key=str):
            if constant in assumption.constants():
                raise ProvisoError(
                    self.name,
                    "{0} is not fresh: it occurs in the undischarged assumption "
                    "{1} of pi_2".format(constant, assumption),
                )
        self._seal(
            pi2.conclusion, (pi1, pi2), (frozenset(), frozenset({instance}))
        )


# --------------------------------------------------------------------------
# Identity
# --------------------------------------------------------------------------


class _EqualityElim(Proof):
    """Shared behaviour of the two directions of identity elimination."""

    __slots__ = ()

    subproof_count = 2
    label = "=E"
    parameters = (
        Parameter(
            "conclusion",
            "formula",
            "pi_2's conclusion with some occurrences of the one constant "
            "replaced by the other",
        ),
    )

    #: True to replace the left constant by the right, False for the reverse.
    forwards = True

    def __init__(self, pi1: Proof, pi2: Proof, conclusion: Formula) -> None:
        identity = _concluding(pi1, Equality, self.name, "pi_1")
        _check_subproof(pi2, self.name, "pi_2")
        _check_formula(conclusion, self.name, "the conclusion")
        old, new = (
            (identity.left, identity.right)
            if self.forwards
            else (identity.right, identity.left)
        )
        if not _replaces_some(pi2.conclusion, conclusion, old, new):
            raise MismatchError(
                self.name,
                "{0} is not {1} with occurrences of {2} replaced by {3}".format(
                    conclusion, pi2.conclusion, old, new
                ),
            )
        self._seal(conclusion, (pi1, pi2))


@register
class EqualityElim1(_EqualityElim):
    """(=Elim1) From c_1 = c_2 and phi infer phi with c_2 put for c_1."""

    __slots__ = ()

    name = "=Elim1"
    forwards = True


@register
class EqualityElim2(_EqualityElim):
    """(=Elim2) From c_1 = c_2 and phi infer phi with c_1 put for c_2."""

    __slots__ = ()

    name = "=Elim2"
    forwards = False
