"""Proofs: the labelled trees of Halbach's natural deduction system.

A proof is a finite tree whose nodes are labelled with *sentences* of L_=.
The root carries the conclusion, the leaves carry the assumptions, and each
non-leaf is an application of an inference rule to the subproofs above it.
The rules themselves live in :mod:`nd.rules`; this module holds the node
they all share, the errors they raise, and the registry a user interface
enumerates them through.

Two features of the reference presentation shape everything here:

* ``As(pi)``, the set of *open* assumptions, is a set of **sentences**, not
  of nodes.  Discharging phi closes every leaf labelled phi in that
  subproof, not just one of them.

* Discharge is uniform.  Every rule that discharges does so by removing a
  set of sentences from the open assumptions of one subproof, so a single
  attribute -- :attr:`Proof.discharged`, a tuple running parallel to
  :attr:`Proof.subproofs` -- expresses the bookkeeping of ``vElim``,
  ``->Intro``, ``~Intro``, ``~Elim``, ``<->Intro`` and ``EElim`` alike.
  It is also what the renderer reads to place the ``[phi]`` markers.

Proofs are immutable, hashable and validated at construction: holding a
:class:`Proof` means holding a proof.  A rule that does not apply raises
rather than building something invalid, and :func:`can_apply` gives the
same verdict without raising, for callers that want to offer a rule and
explain why it is unavailable.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import (
    Dict,
    FrozenSet,
    Iterable,
    Iterator,
    List,
    Optional,
    Sequence,
    Tuple,
    Type,
)

from nd.formula import Constant, Formula, FormulaError, Variable

__all__ = [
    "ProofError",
    "SentenceError",
    "RuleError",
    "ShapeError",
    "MismatchError",
    "ProvisoError",
    "Parameter",
    "Proof",
    "register",
    "rule",
    "rule_catalogue",
    "apply",
    "can_apply",
]


# --------------------------------------------------------------------------
# Errors
# --------------------------------------------------------------------------


class ProofError(Exception):
    """Base class for every error raised by the deduction layer."""


class SentenceError(ProofError):
    """A formula with a free variable was offered as a line of a proof.

    Every node of a proof is a sentence, so ``Fx`` cannot label one; the
    quantifier rules work through constants instead.
    """


class RuleError(ProofError):
    """A rule was applied where it does not apply.

    Carries the rule's name separately from the explanation, so a caller
    can present the two differently.
    """

    def __init__(self, rule_name: str, message: str) -> None:
        self.rule_name = rule_name
        self.message = message
        super().__init__("{0}: {1}".format(rule_name, message))


class ShapeError(RuleError):
    """A subproof's conclusion has the wrong main connective.

    Applying ``^Elim1`` to a proof of a disjunction, for instance.
    """


class MismatchError(RuleError):
    """The subproofs have the right shapes but do not fit together.

    Applying ``->Elim`` where the antecedent of the conditional is not
    what the other subproof concludes, for instance.
    """


class ProvisoError(RuleError):
    """A side condition failed.

    The restrictions on ``AIntro`` and ``EElim``: the parameter must be
    arbitrary, which is to say absent from the conclusion and from the
    assumptions the proof still rests on.
    """


# --------------------------------------------------------------------------
# Rule metadata
# --------------------------------------------------------------------------


@dataclass(frozen=True)
class Parameter:
    """An argument a rule needs besides its subproofs.

    ``vIntro1`` must be told which disjunct to add, ``->Intro`` which
    assumption to discharge, ``EIntro`` which existential is being claimed.
    None of these is recoverable from the subproofs, so each rule declares
    them and a user interface can ask for exactly what is missing.
    """

    name: str
    kind: str  # "formula", "constant" or "variable"
    description: str
    required: bool = True


# --------------------------------------------------------------------------
# The proof node
# --------------------------------------------------------------------------


def _check_formula(value: object, rule_name: str, role: str) -> None:
    if isinstance(value, Formula):
        return
    hint = ""
    if isinstance(value, str):
        hint = "; write Formula.parse({0!r})".format(value)
    raise TypeError(
        "{0}: {1} must be a Formula, not {2}{3}".format(
            rule_name, role, type(value).__name__, hint
        )
    )


def _check_constant(value: object, rule_name: str, role: str) -> None:
    if isinstance(value, Constant):
        return
    hint = ""
    if isinstance(value, str):
        hint = "; write Constant({0!r})".format(value)
    elif isinstance(value, Variable):
        hint = "; the quantifier rules take constants as parameters, not variables"
    raise TypeError(
        "{0}: {1} must be a Constant, not {2}{3}".format(
            rule_name, role, type(value).__name__, hint
        )
    )


def _check_variable(value: object, rule_name: str, role: str) -> None:
    if isinstance(value, Variable):
        return
    hint = ""
    if isinstance(value, str):
        hint = "; write Variable({0!r})".format(value)
    raise TypeError(
        "{0}: {1} must be a Variable, not {2}{3}".format(
            rule_name, role, type(value).__name__, hint
        )
    )


def _check_subproof(value: object, rule_name: str, role: str) -> None:
    if isinstance(value, Proof):
        return
    hint = ""
    if isinstance(value, Formula):
        hint = "; wrap it as Assumption({0})".format(value)
    raise TypeError(
        "{0}: {1} must be a Proof, not {2}{3}".format(
            rule_name, role, type(value).__name__, hint
        )
    )


class Proof:
    """One node of a proof tree, together with everything above it.

    Subclasses -- one per inference rule, in :mod:`nd.rules` -- check their
    own applicability and then call :meth:`_seal`, which does the
    bookkeeping.  The public attributes are:

    ``conclusion``
        the sentence labelling this node.

    ``subproofs``
        the proofs of the immediate premises, in the order the reference
        numbers them.

    ``discharged``
        parallel to ``subproofs``: the set of sentences this application
        closes in each one.

    ``assumptions``
        ``As(pi)``, the sentences the conclusion still rests on.
    """

    __slots__ = ("conclusion", "subproofs", "discharged", "assumptions", "_key", "_hash")

    #: As the reference writes it, e.g. "^Intro".
    name = ""
    #: Short form for the annotation beside an inference bar, e.g. "^I".
    label = ""
    #: How many subproofs the rule takes.
    subproof_count = 0
    #: Arguments beyond the subproofs.
    parameters: Tuple[Parameter, ...] = ()

    # -- construction ------------------------------------------------------

    def _seal(
        self,
        conclusion: Formula,
        subproofs: Sequence["Proof"] = (),
        discharged: Optional[Sequence[Iterable[Formula]]] = None,
        assumptions: Optional[Iterable[Formula]] = None,
    ) -> None:
        """Fix this node's contents and compute its open assumptions.

        ``assumptions`` is given only by the two leaf rules; everywhere
        else it follows from the subproofs and what this step discharges.
        """
        _check_formula(conclusion, self.name, "the conclusion")
        if not conclusion.is_sentence():
            free = ", ".join(sorted(str(v) for v in conclusion.free_variables()))
            raise SentenceError(
                "every line of a proof is a sentence, but {0} has {1} free"
                .format(conclusion, free)
            )

        subproofs = tuple(subproofs)
        for index, subproof in enumerate(subproofs):
            _check_subproof(subproof, self.name, "subproof {0}".format(index + 1))

        if discharged is None:
            closed: Tuple[FrozenSet[Formula], ...] = tuple(
                frozenset() for _ in subproofs
            )
        else:
            closed = tuple(frozenset(group) for group in discharged)
            if len(closed) != len(subproofs):
                raise ValueError(
                    "{0}: {1} subproofs but {2} discharge sets".format(
                        self.name, len(subproofs), len(closed)
                    )
                )

        if assumptions is None:
            open_assumptions: FrozenSet[Formula] = frozenset()
            for subproof, group in zip(subproofs, closed):
                open_assumptions |= subproof.assumptions - group
        else:
            open_assumptions = frozenset(assumptions)

        key = (self.__class__, conclusion, subproofs, closed)
        object.__setattr__(self, "conclusion", conclusion)
        object.__setattr__(self, "subproofs", subproofs)
        object.__setattr__(self, "discharged", closed)
        object.__setattr__(self, "assumptions", open_assumptions)
        object.__setattr__(self, "_key", key)
        object.__setattr__(self, "_hash", hash(key))

    def __setattr__(self, name: str, value) -> None:
        raise AttributeError("a proof is immutable")

    def __delattr__(self, name: str) -> None:
        raise AttributeError("a proof is immutable")

    # -- structure ---------------------------------------------------------

    @property
    def is_leaf(self) -> bool:
        return not self.subproofs

    def nodes(self) -> Iterator["Proof"]:
        """This proof and every proof above it, root first."""
        yield self
        for subproof in self.subproofs:
            for node in subproof.nodes():
                yield node

    def leaves(self) -> Iterator["Proof"]:
        """The nodes with nothing above them: the assumptions and ``=Intro``."""
        for node in self.nodes():
            if node.is_leaf:
                yield node

    def length(self) -> int:
        """``lh(pi)``: the number of nodes on the longest branch."""
        if not self.subproofs:
            return 1
        return 1 + max(subproof.length() for subproof in self.subproofs)

    def size(self) -> int:
        """The number of nodes in the whole tree."""
        return 1 + sum(subproof.size() for subproof in self.subproofs)

    def constants(self) -> FrozenSet[Constant]:
        """Every constant occurring anywhere in the proof.

        The provisos are stated over the conclusion and the open
        assumptions, not over this; it is here for choosing a parameter
        that appears nowhere yet.
        """
        found: FrozenSet[Constant] = frozenset()
        for node in self.nodes():
            found |= node.conclusion.constants()
        return found

    def predicates(self) -> FrozenSet[Tuple[str, int]]:
        """Every predicate used, as ``(name, arity)`` pairs."""
        found: FrozenSet[Tuple[str, int]] = frozenset()
        for node in self.nodes():
            found |= node.conclusion.predicates()
        return found

    def proves(
        self, conclusion: Formula, gamma: Iterable[Formula] = ()
    ) -> bool:
        """True if this establishes ``gamma |- conclusion``.

        That is, it concludes with ``conclusion`` and every assumption it
        still rests on lies in ``gamma``.  With ``gamma`` omitted this asks
        whether the conclusion is a theorem.
        """
        return self.conclusion == conclusion and self.assumptions <= frozenset(gamma)

    def is_theorem(self) -> bool:
        """True if nothing is left undischarged."""
        return not self.assumptions

    # -- comparison --------------------------------------------------------

    def __eq__(self, other) -> bool:
        if not isinstance(other, Proof):
            return NotImplemented
        return self._key == other._key

    def __hash__(self) -> int:
        return self._hash

    # -- printing ----------------------------------------------------------

    def __repr__(self) -> str:
        return "<{0} |- {1}>".format(self.name or self.__class__.__name__, self.conclusion)

    def __str__(self) -> str:
        """The proof drawn as a tree, in the style of the book.

        The import is deferred because :mod:`nd.render` imports this
        module -- the same reason :meth:`nd.formula.Formula.parse` defers
        its import of the parser.
        """
        from nd.render import to_text

        return to_text(self)


# --------------------------------------------------------------------------
# The registry
# --------------------------------------------------------------------------

# Rules are looked up by either spelling: "^Intro" as the book writes it,
# and "AndIntro" as Python spells it.  A user interface builds its palette
# from the catalogue, and reaches a rule through apply()/can_apply()
# without importing the class.

_RULES: Dict[str, Type[Proof]] = {}
_CATALOGUE: List[Type[Proof]] = []


def register(cls: Type[Proof]) -> Type[Proof]:
    """Class decorator adding a rule to the registry."""
    for key in (cls.name, cls.__name__):
        if key in _RULES and _RULES[key] is not cls:
            raise ValueError("two rules registered as {0!r}".format(key))
        _RULES[key] = cls
    _CATALOGUE.append(cls)
    return cls


def rule(name: str) -> Type[Proof]:
    """The rule class registered under ``name``, in either spelling."""
    try:
        return _RULES[name]
    except KeyError:
        known = ", ".join(sorted(cls.name for cls in _CATALOGUE))
        raise KeyError("no rule named {0!r}; there are {1}".format(name, known))


def rule_catalogue() -> Tuple[Type[Proof], ...]:
    """Every rule, in the order the reference introduces them."""
    return tuple(_CATALOGUE)


def apply(rule_name: str, subproofs: Sequence[Proof] = (), **parameters) -> Proof:
    """Build a proof by naming a rule: ``apply("^Intro", [p, q])``."""
    return rule(rule_name)(*subproofs, **parameters)


def can_apply(
    rule_name: str, subproofs: Sequence[Proof] = (), **parameters
) -> Optional[Exception]:
    """The error :func:`apply` would raise, or ``None`` if it would succeed.

    Written as :func:`apply` in a ``try``, so the two can never disagree:
    an interface can grey out a rule and show the reason on hover, and
    know that the reason is the one it would actually get.
    """
    try:
        apply(rule_name, subproofs, **parameters)
    except (ProofError, FormulaError) as error:
        return error
    return None
