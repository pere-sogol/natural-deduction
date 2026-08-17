"""The language L_= : predicate logic with identity.

This module defines terms and formulae for the language used in Volker
Halbach's *The Logic Manual* (Oxford), together with the operations that
Halbach's natural deduction rules depend on.

Two features of that system shape the design:

* The quantifier rules use **constants as parameters**.  Universal
  introduction goes from ``phi(a)`` to ``Ax phi(x)`` provided ``a`` occurs
  neither in the conclusion nor in any undischarged assumption, so every
  line of a proof is a *sentence*.  Hence :meth:`Formula.generalise` (the
  inverse of substitution) and :meth:`Formula.constants` sit alongside
  :meth:`Formula.substitute`.

* There is **no absurdity sign**.  Negation introduction and elimination
  discharge an assumption and yield a negation directly from a
  contradictory pair, so the language needs no ``Falsum``.

Terms are variables and constants only; L_= as presented in the Manual has
no function symbols.  :class:`Term` is nonetheless an abstract base, so a
``Function`` subclass could be added later without disturbing the formula
layer.
"""

from __future__ import annotations

import itertools
import re
from abc import ABC, abstractmethod
from dataclasses import dataclass
from typing import Dict, FrozenSet, Iterable, Iterator, Tuple

__all__ = [
    "FormulaError",
    "ArityError",
    "CaptureError",
    "Term",
    "Variable",
    "Constant",
    "Formula",
    "Atom",
    "Equality",
    "Not",
    "And",
    "Or",
    "Implies",
    "Iff",
    "Quantified",
    "Forall",
    "Exists",
    "fresh_variable",
    "fresh_constant",
    "reset_arities",
    "declared_arities",
]


# --------------------------------------------------------------------------
# Errors
# --------------------------------------------------------------------------


class FormulaError(Exception):
    """Base class for every error raised by this module."""


class ArityError(FormulaError):
    """A predicate letter was used with two different arities."""


class CaptureError(FormulaError):
    """A substitution would have captured a variable.

    Raised when the textbook proviso "t is free for v in phi" fails, so an
    invalid application of a quantifier rule is reported rather than being
    silently repaired by renaming.
    """


# --------------------------------------------------------------------------
# Symbols
# --------------------------------------------------------------------------

NOT = "¬"
AND = "∧"
OR = "∨"
IMPLIES = "→"
IFF = "↔"
FORALL = "∀"
EXISTS = "∃"

# Binding strength, used to decide where brackets are needed when printing.
# Higher binds tighter.  Quantifiers and negation take the smallest scope
# they can, so 'Ax Fx -> Gx' means '(Ax Fx) -> Gx'.
_PREC_ATOM = 4
_PREC_UNARY = 3
_PREC_AND = 2
_PREC_OR = 1
_PREC_ARROW = 0


# --------------------------------------------------------------------------
# Arity registry
# --------------------------------------------------------------------------

_ARITIES: Dict[str, int] = {}


def reset_arities() -> None:
    """Forget every recorded predicate arity.

    Arities accumulate in module-level state, so tests should call this in
    ``setUp`` to stop one case leaking into the next.
    """
    _ARITIES.clear()


def declared_arities() -> Dict[str, int]:
    """A copy of the recorded predicate arities."""
    return dict(_ARITIES)


def _record_arity(predicate: str, arity: int) -> None:
    previous = _ARITIES.get(predicate)
    if previous is None:
        _ARITIES[predicate] = arity
    elif previous != arity:
        raise ArityError(
            "predicate {0!r} used with arity {1}, but was previously used "
            "with arity {2}".format(predicate, arity, previous)
        )


# --------------------------------------------------------------------------
# Terms
# --------------------------------------------------------------------------


class Term(ABC):
    """A variable or a constant.

    Which subclass you instantiate settles whether a symbol is a variable
    or a constant; names are not policed, so ``Variable("a")`` is legal
    even though Halbach's conventions reserve the early letters of the
    alphabet for constants.
    """

    __slots__ = ()

    @abstractmethod
    def free_variables(self) -> FrozenSet["Variable"]:
        """The variables occurring in this term."""

    @abstractmethod
    def constants(self) -> FrozenSet["Constant"]:
        """The constants occurring in this term."""

    @abstractmethod
    def substitute(self, variable: "Variable", term: "Term") -> "Term":
        """Replace ``variable`` by ``term``."""

    @abstractmethod
    def replace_constant(self, constant: "Constant", variable: "Variable") -> "Term":
        """Replace ``constant`` by ``variable``."""


@dataclass(frozen=True)
class Variable(Term):
    """An individual variable, written ``x``, ``y``, ``z``, ``x_1``, ..."""

    name: str

    def free_variables(self) -> FrozenSet["Variable"]:
        return frozenset({self})

    def constants(self) -> FrozenSet["Constant"]:
        return frozenset()

    def substitute(self, variable: "Variable", term: Term) -> Term:
        return term if self == variable else self

    def replace_constant(self, constant: "Constant", variable: "Variable") -> Term:
        return self

    def __str__(self) -> str:
        return self.name

    def __repr__(self) -> str:
        return "Variable({0!r})".format(self.name)


@dataclass(frozen=True)
class Constant(Term):
    """An individual constant, written ``a``, ``b``, ``c``, ``a_1``, ...

    In Halbach's system constants double as the parameters of the
    quantifier rules, which is why :meth:`Formula.generalise` exists.
    """

    name: str

    def free_variables(self) -> FrozenSet[Variable]:
        return frozenset()

    def constants(self) -> FrozenSet["Constant"]:
        return frozenset({self})

    def substitute(self, variable: Variable, term: Term) -> Term:
        return self

    def replace_constant(self, constant: "Constant", variable: Variable) -> Term:
        return variable if self == constant else self

    def __str__(self) -> str:
        return self.name

    def __repr__(self) -> str:
        return "Constant({0!r})".format(self.name)


_SUBSCRIPTED = re.compile(r"^(.*?)_(\d+)$")


def _fresh_name(stem: str, taken: FrozenSet[str]) -> str:
    match = _SUBSCRIPTED.match(stem)
    if match:
        stem = match.group(1)
    if stem not in taken:
        return stem
    for index in itertools.count(1):
        candidate = "{0}_{1}".format(stem, index)
        if candidate not in taken:
            return candidate
    raise AssertionError("unreachable")  # pragma: no cover


def fresh_variable(avoid: Iterable[Term], stem: str = "x") -> Variable:
    """A variable named ``stem`` (or ``stem_1``, ...) unused in ``avoid``."""
    taken = frozenset(term.name for term in avoid if isinstance(term, Variable))
    return Variable(_fresh_name(stem, taken))


def fresh_constant(avoid: Iterable[Term], stem: str = "a") -> Constant:
    """A constant named ``stem`` (or ``stem_1``, ...) unused in ``avoid``.

    Existential elimination needs a parameter occurring nowhere else, so
    pass it the constants of the premises and of every undischarged
    assumption.
    """
    taken = frozenset(term.name for term in avoid if isinstance(term, Constant))
    return Constant(_fresh_name(stem, taken))


# --------------------------------------------------------------------------
# Formulae
# --------------------------------------------------------------------------


class Formula(ABC):
    """A formula of L_=.

    Formulae are immutable and hashable, so they can be collected in the
    sets of undischarged assumptions that the deduction rules maintain.

    Equality is *structural*, not up to renaming of bound variables:
    ``Forall(x, Fx) != Forall(y, Fy)``.  That is the right default for a
    proof checker, since the two are distinct formulae that merely happen
    to be interderivable; :meth:`alpha_equivalent` gives the looser
    comparison where it is wanted.
    """

    __slots__ = ()

    # -- structure ---------------------------------------------------------

    @abstractmethod
    def free_variables(self) -> FrozenSet[Variable]:
        """The variables with a free occurrence in this formula."""

    @abstractmethod
    def bound_variables(self) -> FrozenSet[Variable]:
        """The variables bound by some quantifier in this formula.

        A variable can appear in both this set and
        :meth:`free_variables`: in ``Fx & Ax Gx`` the variable ``x``
        occurs free in the left conjunct and bound in the right.
        """

    @abstractmethod
    def constants(self) -> FrozenSet[Constant]:
        """The constants occurring in this formula.

        This is what the provisos on universal introduction and
        existential elimination are checked against.
        """

    @abstractmethod
    def predicates(self) -> FrozenSet[Tuple[str, int]]:
        """The predicate letters used, as ``(name, arity)`` pairs."""

    @abstractmethod
    def subformulas(self) -> Iterator["Formula"]:
        """This formula and all of its subformulae, outermost first."""

    def variables(self) -> FrozenSet[Variable]:
        """Every variable occurring in this formula, free or bound."""
        return self.free_variables() | self.bound_variables()

    def is_sentence(self) -> bool:
        """True if no variable occurs free.

        Every line of a Halbach-style proof is a sentence.
        """
        return not self.free_variables()

    # -- substitution and binding -----------------------------------------

    @abstractmethod
    def _substitute(self, variable: Variable, term: Term) -> "Formula":
        """Substitute without checking the proviso."""

    @abstractmethod
    def is_free_for(self, term: Term, variable: Variable) -> bool:
        """True if ``term`` is free for ``variable`` in this formula.

        That is, no free occurrence of ``variable`` lies within the scope
        of a quantifier binding a variable of ``term``, so replacing
        ``variable`` by ``term`` would capture nothing.  This is the
        proviso attached to universal elimination and existential
        introduction.
        """

    def substitute(self, variable: Variable, term: Term) -> "Formula":
        """Replace every *free* occurrence of ``variable`` by ``term``.

        Universal elimination in the forward direction, and the check for
        existential introduction in reverse: a conclusion ``Ex phi`` follows
        from a premise ``psi`` exactly when ``phi.substitute(x, t) == psi``
        for some term ``t``.

        Raises :class:`CaptureError` if ``term`` is not free for
        ``variable`` here; nothing is ever renamed behind your back.
        """
        if not self.is_free_for(term, variable):
            raise CaptureError(
                "{0} is not free for {1} in {2}".format(term, variable, self)
            )
        return self._substitute(variable, term)

    @abstractmethod
    def replace_constant(self, constant: Constant, variable: Variable) -> "Formula":
        """Replace every occurrence of ``constant`` by ``variable``.

        The inverse of substitution, and the primitive behind
        :meth:`generalise`.  Raises :class:`CaptureError` if the constant
        occurs within the scope of a quantifier already binding
        ``variable``, since the new occurrence would be captured.
        """

    @abstractmethod
    def replace_term(self, old: Term, new: Term) -> "Formula":
        """Replace every free occurrence of ``old`` by ``new``.

        Unlike :meth:`substitute` this accepts any term on the left, which
        is what the identity rules need: from ``a=b`` and ``phi(a)`` infer
        ``phi(b)``.  Raises :class:`CaptureError` on capture.
        """

    def generalise(
        self, constant: Constant, variable: Variable, quantifier: str = "all"
    ) -> "Formula":
        """Abstract on ``constant`` and bind the result with a quantifier.

        Universal introduction in the forward direction: ``Fa`` generalises
        to ``Ax Fx``.  ``quantifier`` is ``"all"`` or ``"exists"``.

        Replacing *every* occurrence is correct for universal introduction,
        where the proviso guarantees the parameter is fully abstracted.  It
        is not the general shape of existential introduction, which may
        abstract only some occurrences -- from ``Raa`` one may infer
        ``Ex Rxa`` as well as ``Ex Rxx``.  Check those with
        :meth:`substitute` against the proposed conclusion instead.
        """
        body = self.replace_constant(constant, variable)
        if quantifier == "all":
            return Forall(variable, body)
        if quantifier == "exists":
            return Exists(variable, body)
        raise ValueError(
            "quantifier must be 'all' or 'exists', not {0!r}".format(quantifier)
        )

    def alpha_equivalent(self, other: "Formula") -> bool:
        """True if this formula and ``other`` differ only in bound names."""
        return self._de_bruijn(()) == other._de_bruijn(())

    @abstractmethod
    def _de_bruijn(self, binders: Tuple[Variable, ...]):
        """A representation in which bound names carry no information.

        ``binders`` lists the enclosing quantified variables, innermost
        last; a bound variable is rendered as its distance from its
        binder, so alpha-variants normalise to the same value.
        """

    # -- construction ------------------------------------------------------

    def __invert__(self) -> "Formula":
        return Not(self)

    def __and__(self, other: "Formula") -> "Formula":
        return And(self, other)

    def __or__(self, other: "Formula") -> "Formula":
        return Or(self, other)

    def implies(self, other: "Formula") -> "Formula":
        """The conditional with this formula as antecedent.

        Spelled out rather than given to ``>>``, because Python binds
        ``>>`` more tightly than ``&`` and ``|``: ``p & q >> r`` would
        quietly parse as ``p & (q >> r)``.
        """
        return Implies(self, other)

    def iff(self, other: "Formula") -> "Formula":
        """The biconditional of this formula with ``other``."""
        return Iff(self, other)

    # -- printing ----------------------------------------------------------

    @abstractmethod
    def _render(self, parent_precedence: int) -> str:
        """Render, bracketing only where the context requires it."""

    def __str__(self) -> str:
        return self._render(_PREC_ARROW)


def _bracket(text: str, precedence: int, parent_precedence: int) -> str:
    return "({0})".format(text) if precedence < parent_precedence else text


class Atom(Formula):
    """An atomic formula: ``Fx``, ``Rxy``, or a sentence letter ``P``.

    Terms are given as separate arguments, following the book's
    juxtaposition notation.  A predicate letter's arity is fixed by its
    first use and checked on every use thereafter, so writing ``Rx`` where
    ``Rxy`` was meant is caught immediately.
    """

    __slots__ = ("predicate", "terms")

    def __init__(self, predicate: str, *terms: Term) -> None:
        _record_arity(predicate, len(terms))
        object.__setattr__(self, "predicate", predicate)
        object.__setattr__(self, "terms", tuple(terms))

    def __setattr__(self, name: str, value) -> None:
        raise AttributeError("Atom is immutable")

    def __delattr__(self, name: str) -> None:
        raise AttributeError("Atom is immutable")

    @property
    def arity(self) -> int:
        return len(self.terms)

    def free_variables(self) -> FrozenSet[Variable]:
        return frozenset().union(*[t.free_variables() for t in self.terms])

    def bound_variables(self) -> FrozenSet[Variable]:
        return frozenset()

    def constants(self) -> FrozenSet[Constant]:
        return frozenset().union(*[t.constants() for t in self.terms])

    def predicates(self) -> FrozenSet[Tuple[str, int]]:
        return frozenset({(self.predicate, self.arity)})

    def subformulas(self) -> Iterator[Formula]:
        yield self

    def is_free_for(self, term: Term, variable: Variable) -> bool:
        return True

    def _substitute(self, variable: Variable, term: Term) -> Formula:
        return Atom(self.predicate, *(t.substitute(variable, term) for t in self.terms))

    def replace_constant(self, constant: Constant, variable: Variable) -> Formula:
        return Atom(
            self.predicate,
            *(t.replace_constant(constant, variable) for t in self.terms),
        )

    def replace_term(self, old: Term, new: Term) -> Formula:
        return Atom(
            self.predicate, *(new if t == old else t for t in self.terms)
        )

    def _de_bruijn(self, binders: Tuple[Variable, ...]):
        return ("atom", self.predicate, tuple(_term_index(t, binders) for t in self.terms))

    def _render(self, parent_precedence: int) -> str:
        return self.predicate + "".join(str(t) for t in self.terms)

    def __eq__(self, other) -> bool:
        if other.__class__ is not Atom:
            return NotImplemented
        return self.predicate == other.predicate and self.terms == other.terms

    def __hash__(self) -> int:
        return hash((Atom, self.predicate, self.terms))

    def __repr__(self) -> str:
        arguments = "".join(", " + repr(t) for t in self.terms)
        return "Atom({0!r}{1})".format(self.predicate, arguments)


@dataclass(frozen=True)
class Equality(Formula):
    """An identity statement ``t=s``.

    Kept distinct from :class:`Atom` so that it prints infix and the
    identity rules can recognise it without inspecting predicate names.
    """

    left: Term
    right: Term

    def free_variables(self) -> FrozenSet[Variable]:
        return self.left.free_variables() | self.right.free_variables()

    def bound_variables(self) -> FrozenSet[Variable]:
        return frozenset()

    def constants(self) -> FrozenSet[Constant]:
        return self.left.constants() | self.right.constants()

    def predicates(self) -> FrozenSet[Tuple[str, int]]:
        return frozenset()

    def subformulas(self) -> Iterator[Formula]:
        yield self

    def is_free_for(self, term: Term, variable: Variable) -> bool:
        return True

    def _substitute(self, variable: Variable, term: Term) -> Formula:
        return Equality(
            self.left.substitute(variable, term),
            self.right.substitute(variable, term),
        )

    def replace_constant(self, constant: Constant, variable: Variable) -> Formula:
        return Equality(
            self.left.replace_constant(constant, variable),
            self.right.replace_constant(constant, variable),
        )

    def replace_term(self, old: Term, new: Term) -> Formula:
        return Equality(
            new if self.left == old else self.left,
            new if self.right == old else self.right,
        )

    def _de_bruijn(self, binders: Tuple[Variable, ...]):
        return ("=", _term_index(self.left, binders), _term_index(self.right, binders))

    def _render(self, parent_precedence: int) -> str:
        return "{0}={1}".format(self.left, self.right)

    def __repr__(self) -> str:
        return "Equality({0!r}, {1!r})".format(self.left, self.right)


@dataclass(frozen=True)
class Not(Formula):
    """A negation."""

    sub: Formula

    def free_variables(self) -> FrozenSet[Variable]:
        return self.sub.free_variables()

    def bound_variables(self) -> FrozenSet[Variable]:
        return self.sub.bound_variables()

    def constants(self) -> FrozenSet[Constant]:
        return self.sub.constants()

    def predicates(self) -> FrozenSet[Tuple[str, int]]:
        return self.sub.predicates()

    def subformulas(self) -> Iterator[Formula]:
        yield self
        for formula in self.sub.subformulas():
            yield formula

    def is_free_for(self, term: Term, variable: Variable) -> bool:
        return self.sub.is_free_for(term, variable)

    def _substitute(self, variable: Variable, term: Term) -> Formula:
        return Not(self.sub._substitute(variable, term))

    def replace_constant(self, constant: Constant, variable: Variable) -> Formula:
        return Not(self.sub.replace_constant(constant, variable))

    def replace_term(self, old: Term, new: Term) -> Formula:
        return Not(self.sub.replace_term(old, new))

    def _de_bruijn(self, binders: Tuple[Variable, ...]):
        return ("not", self.sub._de_bruijn(binders))

    def _render(self, parent_precedence: int) -> str:
        return _bracket(
            NOT + self.sub._render(_PREC_UNARY), _PREC_UNARY, parent_precedence
        )

    def __repr__(self) -> str:
        return "Not({0!r})".format(self.sub)


class _Binary(Formula):
    """Shared behaviour of the two-place connectives."""

    __slots__ = ()

    #: Filled in by each subclass.
    symbol = ""
    precedence = _PREC_ARROW
    right_associative = False

    def free_variables(self) -> FrozenSet[Variable]:
        return self.left.free_variables() | self.right.free_variables()

    def bound_variables(self) -> FrozenSet[Variable]:
        return self.left.bound_variables() | self.right.bound_variables()

    def constants(self) -> FrozenSet[Constant]:
        return self.left.constants() | self.right.constants()

    def predicates(self) -> FrozenSet[Tuple[str, int]]:
        return self.left.predicates() | self.right.predicates()

    def subformulas(self) -> Iterator[Formula]:
        yield self
        for formula in self.left.subformulas():
            yield formula
        for formula in self.right.subformulas():
            yield formula

    def is_free_for(self, term: Term, variable: Variable) -> bool:
        return self.left.is_free_for(term, variable) and self.right.is_free_for(
            term, variable
        )

    def _substitute(self, variable: Variable, term: Term) -> Formula:
        return self.__class__(
            self.left._substitute(variable, term),
            self.right._substitute(variable, term),
        )

    def replace_constant(self, constant: Constant, variable: Variable) -> Formula:
        return self.__class__(
            self.left.replace_constant(constant, variable),
            self.right.replace_constant(constant, variable),
        )

    def replace_term(self, old: Term, new: Term) -> Formula:
        return self.__class__(
            self.left.replace_term(old, new), self.right.replace_term(old, new)
        )

    def _de_bruijn(self, binders: Tuple[Variable, ...]):
        return (
            self.symbol,
            self.left._de_bruijn(binders),
            self.right._de_bruijn(binders),
        )

    def _render(self, parent_precedence: int) -> str:
        # A right-associative connective needs no brackets on its right
        # branch when the two are equally tight, and vice versa.
        if self.right_associative:
            left_context, right_context = self.precedence + 1, self.precedence
        else:
            left_context, right_context = self.precedence, self.precedence + 1
        text = "{0} {1} {2}".format(
            self.left._render(left_context),
            self.symbol,
            self.right._render(right_context),
        )
        return _bracket(text, self.precedence, parent_precedence)

    def __repr__(self) -> str:
        return "{0}({1!r}, {2!r})".format(
            self.__class__.__name__, self.left, self.right
        )


# ``repr=False`` on each of these keeps the hand-written ``__repr__`` from
# the shared base; dataclass would otherwise install its own.


@dataclass(frozen=True, repr=False)
class And(_Binary):
    """A conjunction. Also written ``p & q``."""

    left: Formula
    right: Formula

    symbol = AND
    precedence = _PREC_AND
    right_associative = True


@dataclass(frozen=True, repr=False)
class Or(_Binary):
    """A disjunction. Also written ``p | q``."""

    left: Formula
    right: Formula

    symbol = OR
    precedence = _PREC_OR
    right_associative = True


@dataclass(frozen=True, repr=False)
class Implies(_Binary):
    """A conditional. Also written ``p.implies(q)``."""

    left: Formula
    right: Formula

    symbol = IMPLIES
    precedence = _PREC_ARROW
    right_associative = True


@dataclass(frozen=True, repr=False)
class Iff(_Binary):
    """A biconditional. Also written ``p.iff(q)``."""

    left: Formula
    right: Formula

    symbol = IFF
    precedence = _PREC_ARROW
    right_associative = True


class Quantified(Formula):
    """Shared behaviour of the two quantifiers."""

    __slots__ = ()

    #: Filled in by each subclass.
    symbol = ""

    def free_variables(self) -> FrozenSet[Variable]:
        return self.body.free_variables() - {self.variable}

    def bound_variables(self) -> FrozenSet[Variable]:
        return self.body.bound_variables() | {self.variable}

    def constants(self) -> FrozenSet[Constant]:
        return self.body.constants()

    def predicates(self) -> FrozenSet[Tuple[str, int]]:
        return self.body.predicates()

    def subformulas(self) -> Iterator[Formula]:
        yield self
        for formula in self.body.subformulas():
            yield formula

    def is_free_for(self, term: Term, variable: Variable) -> bool:
        if variable == self.variable:
            # No free occurrence of the variable survives here, so nothing
            # can be captured.
            return True
        if (
            self.variable in term.free_variables()
            and variable in self.body.free_variables()
        ):
            # Substituting would push a variable of the term under this
            # quantifier, which would bind it.
            return False
        return self.body.is_free_for(term, variable)

    def _substitute(self, variable: Variable, term: Term) -> Formula:
        if variable == self.variable:
            return self
        return self.__class__(self.variable, self.body._substitute(variable, term))

    def replace_constant(self, constant: Constant, variable: Variable) -> Formula:
        if variable == self.variable and constant in self.body.constants():
            raise CaptureError(
                "{0} occurs within the scope of {1}{2} in {3}, so replacing it "
                "by {2} would capture it".format(
                    constant, self.symbol, variable, self
                )
            )
        return self.__class__(
            self.variable, self.body.replace_constant(constant, variable)
        )

    def replace_term(self, old: Term, new: Term) -> Formula:
        if old == self.variable:
            return self
        if self.variable in new.free_variables() and old in self.body.free_variables():
            raise CaptureError(
                "replacing {0} by {1} in {2} would capture {3}".format(
                    old, new, self, self.variable
                )
            )
        return self.__class__(self.variable, self.body.replace_term(old, new))

    def _de_bruijn(self, binders: Tuple[Variable, ...]):
        return (self.symbol, self.body._de_bruijn(binders + (self.variable,)))

    def _render(self, parent_precedence: int) -> str:
        body = self.body._render(_PREC_UNARY)
        # A space is only needed to keep the bound variable from running
        # into a predicate letter: 'Ax Fx', but 'Ax(Fx -> Gx)', 'Ax~Fx'
        # and 'AxEy Rxy'.
        separator = "" if body[:1] in "(" + NOT + FORALL + EXISTS else " "
        text = "{0}{1}{2}{3}".format(self.symbol, self.variable, separator, body)
        return _bracket(text, _PREC_UNARY, parent_precedence)

    def __repr__(self) -> str:
        return "{0}({1!r}, {2!r})".format(
            self.__class__.__name__, self.variable, self.body
        )


@dataclass(frozen=True, repr=False)
class Forall(Quantified):
    """A universally quantified formula."""

    variable: Variable
    body: Formula

    symbol = FORALL


@dataclass(frozen=True, repr=False)
class Exists(Quantified):
    """An existentially quantified formula."""

    variable: Variable
    body: Formula

    symbol = EXISTS


def _term_index(term: Term, binders: Tuple[Variable, ...]):
    """Render a term with bound variables replaced by binder distances.

    Free variables and constants keep their names; a bound variable
    becomes its distance from the quantifier binding it, so that formulae
    differing only in the choice of bound names normalise alike.
    """
    if isinstance(term, Variable):
        for distance, binder in enumerate(reversed(binders)):
            if binder == term:
                return ("bound", distance)
        return ("free", term.name)
    return ("const", term.name)


# --------------------------------------------------------------------------
# Demonstration
# --------------------------------------------------------------------------

if __name__ == "__main__":
    x, y = Variable("x"), Variable("y")
    a = Constant("a")

    # Ax (Fx -> Ey Rxy), built with named constructors ...
    claim = Forall(x, Implies(Atom("F", x), Exists(y, Atom("R", x, y))))
    # ... and with operators, where '&', '|' and '~' are available.
    same = Forall(x, Atom("F", x).implies(Exists(y, Atom("R", x, y))))

    print("formula:          ", claim)
    print("built both ways:  ", claim == same)
    print("free variables:   ", set(claim.free_variables()) or "none")
    print("is a sentence:    ", claim.is_sentence())

    # Universal elimination, then universal introduction back again.
    instance = claim.body.substitute(x, a)
    print("instance at a:    ", instance)
    print("constants:        ", set(instance.constants()))
    print("generalised:      ", instance.generalise(a, x))

    # The proviso is reported rather than silently repaired.
    trap = Exists(y, Not(Equality(x, y)))
    print("free for x in {0}: {1}".format(trap, trap.is_free_for(y, x)))
    try:
        trap.substitute(x, y)
    except CaptureError as error:
        print("refused:          ", error)

    # Bracketing follows the usual conventions.
    p, q, r = Atom("P"), Atom("Q"), Atom("S")
    print("smallest scope:   ", Implies(Forall(x, Atom("F", x)), Atom("G", a)))
    print("arrows right-assoc:", Implies(p, Implies(q, r)))
    print("and binds tighter:", Implies(And(p, q), r))
    print("brackets needed:  ", And(p, Implies(q, r)))
    print("negated:          ", Not(Or(p, And(q, r))))
