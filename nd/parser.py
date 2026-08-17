"""Reading formulae of L_= from strings.

``parse("Ax(Fx -> Ey Rxy)")`` builds the same object as nesting the
constructors in :mod:`nd.formula` by hand.  Nothing here adds logical
power; it exists so that proofs and tests can be written readably.

Notation
--------

Both the book's symbols and an ASCII transliteration are accepted, so the
output of ``str()`` parses back unchanged::

    quantifiers   A x     E x        forall, exists
    negation      ~       -
    conjunction   &
    disjunction   |
    conditional   ->
    biconditional <->

Predicate letters are uppercase, terms lowercase, and both may carry a
numeric subscript (``F_1``, ``x_2``).  A term is a **variable** if its
letter is one of ``u v w x y z`` and a **constant** otherwise, so ``Fx``
is open and ``Fa`` is a sentence.  Quantifying a constant letter --
``Ab Fb`` -- is an error rather than a silent reinterpretation.

Atomic formulae may be written by juxtaposition as in the Manual, or with
brackets: ``Rxy`` and ``R(x, y)`` are the same formula.  Brackets are also
the only way to use a name longer than one letter, as in ``Loves(a, b)``,
where the opening bracket must follow the name immediately.

Two points to be aware of:

* Bare ``A`` and ``E`` are the quantifiers, so they cannot double as
  juxtaposed predicate letters.  ``A(x)`` and ``A_1x`` still write the
  predicate, and the Unicode forms leave them free entirely.
* ``v`` is a variable letter, so it does not mean disjunction.  Write
  ``|`` or the Unicode symbol.
"""

from __future__ import annotations

import re
from typing import List, NamedTuple, Sequence

from nd.formula import (
    AND,
    EXISTS,
    FORALL,
    IFF,
    IMPLIES,
    NOT,
    OR,
    And,
    Atom,
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
    Term,
    Variable,
)

__all__ = ["ParseError", "parse", "parse_term", "VARIABLE_LETTERS", "CONSTANT_LETTERS"]

#: Letters read as variables; every other lowercase letter is a constant.
VARIABLE_LETTERS = "uvwxyz"
CONSTANT_LETTERS = "abcdefghijklmnopqrst"


class ParseError(FormulaError):
    """The input was not a well-formed formula.

    Carries the source text and the offending offset, and prints them
    with a caret so the reader can see where parsing stopped.
    """

    def __init__(self, message: str, text: str, position: int) -> None:
        super().__init__(message)
        self.message = message
        self.text = text
        self.position = position

    def __str__(self) -> str:
        return "{0} (column {1})\n\n  {2}\n  {3}^".format(
            self.message, self.position + 1, self.text, " " * self.position
        )


# --------------------------------------------------------------------------
# Tokenising
# --------------------------------------------------------------------------


class _Token(NamedTuple):
    kind: str
    value: str
    position: int


# A maximal run of name characters, split afterwards into single letters
# unless it is immediately applied to a bracketed argument list.
_RUN = re.compile(r"[A-Za-z][A-Za-z0-9_]*")

# One letter with an optional numeric subscript, matching the names that
# ``fresh_variable`` and ``fresh_constant`` generate.
_SINGLE = re.compile(r"[A-Za-z](?:_[0-9]+)?")

# Longest first, so '<->' beats '->' and '->' beats '-'.
_SYMBOLS = (
    ("<->", "IFF"),
    ("->", "IMPLIES"),
    (IFF, "IFF"),
    (IMPLIES, "IMPLIES"),
    (AND, "AND"),
    (OR, "OR"),
    (NOT, "NOT"),
    (FORALL, "FORALL"),
    (EXISTS, "EXISTS"),
    ("&", "AND"),
    ("|", "OR"),
    ("~", "NOT"),
    ("-", "NOT"),
    ("(", "LPAREN"),
    (")", "RPAREN"),
    (",", "COMMA"),
    ("=", "EQUALS"),
)


def _opens_a_quantifier(run: str) -> bool:
    """True if a run should be read as ``A``/``E`` binding a variable.

    Needed because ``Ax(Fx -> Gx)`` and ``Loves(a, b)`` have the same
    shape -- a run of letters applied to brackets.  A bare ``A`` or ``E``
    followed by a variable letter is taken as the quantifier, so a
    multi-letter name may not begin that way; ``Ab(x)`` and ``A_1(x)``
    are still names, since neither is a quantifier reading.
    """
    return len(run) >= 2 and run[0] in "AE" and run[1] in VARIABLE_LETTERS


def _classify(name: str, position: int) -> _Token:
    """Turn one name into a quantifier, predicate or term token."""
    if name == "A":
        return _Token("FORALL", name, position)
    if name == "E":
        return _Token("EXISTS", name, position)
    if name[0].isupper():
        return _Token("PRED", name, position)
    return _Token("TERM", name, position)


def _tokenise(text: str) -> List[_Token]:
    tokens: List[_Token] = []
    index = 0
    length = len(text)
    while index < length:
        if text[index].isspace():
            index += 1
            continue

        run = _RUN.match(text, index)
        if run:
            end = run.end()
            if (
                end < length
                and text[end] == "("
                and run.group(0)[0].isupper()
                and not _opens_a_quantifier(run.group(0))
            ):
                # An uppercase name applied to brackets is taken whole,
                # which is what makes multi-letter predicates possible.
                # A lowercase one is split, so 'Ax(Fx -> Gx)' and the
                # Unicode 'Ax(...)' both reach the quantifier rule.
                tokens.append(_Token("PRED", run.group(0), index))
            else:
                _reject_v_as_disjunction(text, index, end)
                _split_run(text, index, end, tokens)
            index = end
            continue

        for symbol, kind in _SYMBOLS:
            if text.startswith(symbol, index):
                tokens.append(_Token(kind, symbol, index))
                index += len(symbol)
                break
        else:
            raise ParseError(
                "unexpected character {0!r}".format(text[index]), text, index
            )

    tokens.append(_Token("EOF", "", length))
    return tokens


def _reject_v_as_disjunction(text: str, start: int, end: int) -> None:
    """Catch ``P v Q``, where 'v' was meant as the disjunction sign.

    Caught here rather than in the parser because by then the ``v`` has
    been quietly absorbed as an argument of ``P``, and the complaint
    surfaces somewhere unhelpful.  A lone whitespace-delimited ``v`` is
    almost always the handwritten disjunction; a term is written ``Fv``
    or ``F(v)``, not with spaces around it.
    """
    if text[start:end] != "v":
        return
    before_is_space = start > 0 and text[start - 1].isspace()
    after_is_space = end < len(text) and text[end].isspace()
    if before_is_space and after_is_space:
        raise ParseError(
            "{0!r} is a variable letter, not disjunction; write '|' or {1!r} "
            "(and a term as Fv or F(v))".format("v", OR),
            text,
            start,
        )


def _split_run(text: str, start: int, end: int, tokens: List[_Token]) -> None:
    """Split a juxtaposed run such as ``F_1x_2y`` into its names."""
    position = start
    while position < end:
        single = _SINGLE.match(text, position)
        if single is None or single.end() > end:
            raise ParseError(
                "expected a letter; a subscript needs an underscore, as in F_1",
                text,
                position,
            )
        tokens.append(_classify(single.group(0), position))
        position = single.end()


# --------------------------------------------------------------------------
# Parsing
# --------------------------------------------------------------------------


class _Parser:
    """Recursive descent over the token list.

    The grammar mirrors the precedence in :mod:`nd.formula` exactly --
    ``~`` tightest, then ``&``, ``|``, then the two arrows -- so that
    ``parse(str(f)) == f``.
    """

    def __init__(self, tokens: Sequence[_Token], text: str) -> None:
        self.tokens = tokens
        self.text = text
        self.index = 0

    # -- token handling ----------------------------------------------------

    def _peek(self) -> _Token:
        return self.tokens[self.index]

    def _at(self, *kinds: str) -> bool:
        return self._peek().kind in kinds

    def _advance(self) -> _Token:
        token = self.tokens[self.index]
        self.index += 1
        return token

    def _expect(self, kind: str, description: str) -> _Token:
        if not self._at(kind):
            self._error("expected {0}".format(description))
        return self._advance()

    def _error(self, message: str, token: _Token = None) -> None:
        offender = self._peek() if token is None else token
        raise ParseError(message, self.text, offender.position)

    # -- grammar -----------------------------------------------------------

    def formula(self) -> Formula:
        return self._arrow()

    def _arrow(self) -> Formula:
        # Collected iteratively rather than recursively, so that a mixture
        # of the two arrows can be spotted before anything is built.
        operands = [self._disjunction()]
        operators: List[_Token] = []
        while self._at("IMPLIES", "IFF"):
            operator = self._advance()
            if operators and operators[0].kind != operator.kind:
                self._error(
                    "mixing {0} and {1} needs brackets".format(IMPLIES, IFF), operator
                )
            operators.append(operator)
            operands.append(self._disjunction())

        result = operands[-1]
        for operator, left in zip(reversed(operators), reversed(operands[:-1])):
            connective = Implies if operator.kind == "IMPLIES" else Iff
            result = connective(left, result)
        return result

    def _disjunction(self) -> Formula:
        left = self._conjunction()
        if self._at("OR"):
            self._advance()
            return Or(left, self._disjunction())
        return left

    def _conjunction(self) -> Formula:
        left = self._unary()
        if self._at("AND"):
            self._advance()
            return And(left, self._conjunction())
        return left

    def _unary(self) -> Formula:
        if self._at("NOT"):
            self._advance()
            return Not(self._unary())
        if self._at("FORALL", "EXISTS"):
            return self._quantifier()
        return self._primary()

    def _quantifier(self) -> Formula:
        quantifier = self._advance()
        symbol = FORALL if quantifier.kind == "FORALL" else EXISTS
        if not self._at("TERM"):
            message = "expected a variable after {0}".format(symbol)
            if quantifier.value in ("A", "E"):
                message += (
                    "; bare {0!r} is the quantifier, so write {0}(x) for the "
                    "predicate".format(quantifier.value)
                )
            self._error(message)
        variable = self._advance()
        if variable.value[0] not in VARIABLE_LETTERS:
            self._error(
                "{0!r} is a constant letter, so it cannot be quantified; "
                "variables are {1}-{2}".format(
                    variable.value, VARIABLE_LETTERS[0], VARIABLE_LETTERS[-1]
                ),
                variable,
            )
        # The body is a unary, so the quantifier takes the smallest scope:
        # 'Ax Fx -> Gx' is '(Ax Fx) -> Gx'.
        body = self._unary()
        connective = Forall if quantifier.kind == "FORALL" else Exists
        return connective(Variable(variable.value), body)

    def _primary(self) -> Formula:
        if self._at("LPAREN"):
            self._advance()
            inner = self.formula()
            self._expect("RPAREN", "')' to close the bracket")
            return inner
        # Case settles the rest: predicates are uppercase, terms lowercase.
        if self._at("PRED"):
            return self._atom()
        if self._at("TERM"):
            return self._equality()
        if self._at("EOF"):
            self._error("expected a formula but reached the end of the input")
        self._error("expected a formula")

    def _atom(self) -> Formula:
        predicate = self._advance()
        terms: List[Term] = []
        if self._at("LPAREN"):
            self._advance()
            if not self._at("RPAREN"):
                terms.append(self._term())
                while self._at("COMMA"):
                    self._advance()
                    terms.append(self._term())
            self._expect("RPAREN", "')' to close the argument list")
        else:
            while self._at("TERM"):
                terms.append(self._term())
        # Atom() checks the arity against the letter's earlier uses.
        return Atom(predicate.value, *terms)

    def _equality(self) -> Formula:
        left = self._term()
        if self._at("LPAREN"):
            # 'f(x)' looks like a function symbol, which L_= does not have.
            self._error(
                "{0!r} is a term, and L_= has no function symbols, so it cannot "
                "be applied to arguments".format(left.name)
            )
        self._expect("EQUALS", "'=' after a term")
        return Equality(left, self._term())

    def _term(self) -> Term:
        if not self._at("TERM"):
            self._error("expected a term")
        token = self._advance()
        if token.value[0] in VARIABLE_LETTERS:
            return Variable(token.value)
        return Constant(token.value)

    # -- completion --------------------------------------------------------

    def expect_end(self) -> None:
        if self._at("EOF"):
            return
        token = self._peek()
        if token.kind == "TERM" and token.value == "v":
            self._error(
                "{0!r} is a variable letter, not disjunction; write '|' or "
                "{1!r}".format("v", OR),
                token,
            )
        self._error(
            "unexpected {0!r} after a complete formula".format(token.value), token
        )


# --------------------------------------------------------------------------
# Entry points
# --------------------------------------------------------------------------


def parse(text: str) -> Formula:
    """Read a formula, raising :class:`ParseError` if the input is not one.

    Predicate arities are checked as the atoms are built, so an
    :class:`~nd.formula.ArityError` may surface here too.
    """
    parser = _Parser(_tokenise(text), text)
    if parser._at("EOF"):
        raise ParseError("expected a formula but the input was empty", text, 0)
    result = parser.formula()
    parser.expect_end()
    return result


def parse_term(text: str) -> Term:
    """Read a single term, for callers that need one on its own.

    Universal elimination needs the term to instantiate at, and it is
    convenient to be able to read that from a string too.
    """
    parser = _Parser(_tokenise(text), text)
    if parser._at("EOF"):
        raise ParseError("expected a term but the input was empty", text, 0)
    result = parser._term()
    parser.expect_end()
    return result
