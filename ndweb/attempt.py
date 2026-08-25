"""Applying a rule and reporting precisely what went wrong.

:func:`nd.proofs.can_apply` catches ``ProofError`` and ``FormulaError`` --
the errors meaning *this rule does not apply here*.  It deliberately does
not catch a ``TypeError`` from being handed a raw string where a formula
was wanted, a ``KeyError`` from an unknown rule name, or a ``ValueError``.
Those mean the *caller* is wrong, and an editor that reported them as a
refusal would hide its own bug behind a message about logic.

So this module catches both families and keeps them apart: a refusal is
shown to the student in the language of the system, and a mistake by the
editor says so and asks to be reported.  Widening ``can_apply`` instead
would lose that distinction, which is why it stays as it is.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import List, Optional, Sequence, Tuple

from nd.formula import (
    And,
    ArityError,
    CaptureError,
    Formula,
    FormulaError,
    Iff,
    Implies,
    Not,
    Or,
    Quantified,
)
from nd.parser import ParseError
from nd.proofs import (
    MismatchError,
    Proof,
    ProofError,
    ProvisoError,
    SentenceError,
    ShapeError,
    apply,
)

__all__ = ["RuleFailure", "Attempt", "attempt", "BUG_KINDS"]

#: Kinds that mean the editor passed something wrong, not that the rule
#: failed to apply.  Shown differently, because the student cannot fix them.
BUG_KINDS = frozenset({"argument", "unknown-rule", "internal"})


@dataclass(frozen=True)
class RuleFailure:
    """Why a step did not go through.

    ``kind`` is the machine-readable classification, ``message`` the line
    a student reads, and ``detail`` the whole error -- a ``ParseError``
    keeps its caret block there.
    """

    kind: str
    message: str
    detail: str = ""
    rule: str = ""
    node: int = -1

    @property
    def is_bug(self) -> bool:
        return self.kind in BUG_KINDS


@dataclass(frozen=True)
class Attempt:
    """The outcome: exactly one of ``proof`` and ``failure`` is set."""

    proof: Optional[Proof] = None
    failure: Optional[RuleFailure] = None

    @property
    def ok(self) -> bool:
        return self.proof is not None


_RULE_KINDS = (
    (ShapeError, "shape"),
    (MismatchError, "mismatch"),
    (ProvisoError, "proviso"),
    (SentenceError, "sentence"),
    (ParseError, "parse"),
    (ArityError, "arity"),
    (CaptureError, "capture"),
)


def _constituents(formula: Formula) -> List[Formula]:
    """``formula`` and the formulae one level inside it.

    A mismatch is usually between a whole conclusion and a *part* of
    another one -- the antecedent of a conditional, a half of a
    biconditional -- so a hint that only compared conclusions would miss
    the case it is for.
    """
    found = [formula]
    if isinstance(formula, (And, Or, Implies, Iff)):
        found.extend((formula.left, formula.right))
    elif isinstance(formula, Not):
        found.append(formula.sub)
    elif isinstance(formula, Quantified):
        found.append(formula.body)
    return found


def _alpha_hint(subproofs: Sequence[Proof], parameters: Tuple[Formula, ...]) -> str:
    """A note when two formulae differ only in a bound variable's name.

    ``Ax Fx`` and ``Ay Fy`` are distinct formulae here, correctly -- they
    are interderivable rather than identical, and a checker that conflated
    them would accept steps the book does not.  But it is the commonest
    thing for a student to be caught by, so the refusal says so.
    """
    candidates: List[Formula] = []
    for subproof in subproofs:
        candidates.extend(_constituents(subproof.conclusion))
    for parameter in parameters:
        candidates.extend(_constituents(parameter))
    for index, first in enumerate(candidates):
        for second in candidates[index + 1 :]:
            if first != second and first.alpha_equivalent(second):
                return (
                    " -- {0} and {1} differ only in the name of a bound "
                    "variable, which makes them different sentences here"
                    .format(first, second)
                )
    return ""


def attempt(rule_name: str, subproofs: Sequence[Proof] = (), **parameters) -> Attempt:
    """Build a proof, or say why not.

    The signature is :func:`nd.proofs.apply`'s, so a caller that already
    knows how to drive the engine needs no translation.
    """
    try:
        return Attempt(proof=apply(rule_name, subproofs, **parameters))
    except ProofError as error:
        kind = "rule"
        for error_type, name in _RULE_KINDS:
            if isinstance(error, error_type):
                kind = name
                break
        message = getattr(error, "message", None) or str(error)
        if kind == "mismatch":
            formulae = tuple(
                value for value in parameters.values() if isinstance(value, Formula)
            )
            message += _alpha_hint(subproofs, formulae)
        return Attempt(
            failure=RuleFailure(kind, message, str(error), rule_name)
        )
    except FormulaError as error:
        kind = "formula"
        for error_type, name in _RULE_KINDS:
            if isinstance(error, error_type):
                kind = name
                break
        return Attempt(
            failure=RuleFailure(kind, str(error).split("\n")[0], str(error), rule_name)
        )
    except KeyError as error:
        return Attempt(
            failure=RuleFailure(
                "unknown-rule",
                "there is no rule called {0}".format(rule_name),
                str(error),
                rule_name,
            )
        )
    except (TypeError, ValueError) as error:
        kind = "argument" if isinstance(error, TypeError) else "internal"
        return Attempt(
            failure=RuleFailure(
                kind,
                "the editor applied {0} wrongly: {1}".format(rule_name, error),
                str(error),
                rule_name,
            )
        )
