"""Tests for the string reader, nd.parser."""

import unittest

from nd.formula import (
    And,
    ArityError,
    Atom,
    Constant,
    Equality,
    Exists,
    Forall,
    Iff,
    Implies,
    Not,
    Or,
    Variable,
    reset_arities,
)
from nd.parser import ParseError, parse, parse_term


class ParserTestCase(unittest.TestCase):
    """Arities are module-level state, so start each case from a clean one."""

    def setUp(self):
        reset_arities()
        self.x = Variable("x")
        self.y = Variable("y")
        self.a = Constant("a")
        self.b = Constant("b")

    def assertParseError(self, text, *fragments):
        with self.assertRaises(ParseError) as caught:
            parse(text)
        message = str(caught.exception)
        for fragment in fragments:
            self.assertIn(fragment, message)
        return caught.exception


#: One of every construct, in the notation a reader would actually type.
CORPUS = [
    "P",
    "Fx",
    "Fa",
    "Rxy",
    "Rabc",
    "Loves(a, b)",
    "A(x)",
    "E(a)",
    "a=b",
    "~a=b",
    "x=y",
    "~P",
    "~~P",
    "P & Q",
    "P | Q",
    "P -> Q",
    "P <-> Q",
    "P & Q | S",
    "P | Q & S",
    "~P & Q",
    "P & Q -> S",
    "P -> Q -> S",
    "(P -> Q) -> S",
    "P <-> Q <-> S",
    "P -> (Q <-> S)",
    "(P -> Q) <-> S",
    "Ax Fx",
    "Ey Fy",
    "Ax ~Fx",
    "Ax(Fx -> Gx)",
    "Ax Fx -> Gx",
    "Ax Ey Rxy",
    "Ax Ey ~x=y",
    "Ax Ey (Fx & Gy | ~Rxy)",
    "Ax Ax Fx",
    "Fx & Ax Gx",
    "F_1x_2",
    "A_1x",
]


class TestRoundTrip(ParserTestCase):
    """The printer's output must read back as the same formula.

    This is what keeps parser and printer from drifting apart on
    precedence, bracketing or the reserved quantifier letters.
    """

    def test_round_trip(self):
        for text in CORPUS:
            with self.subTest(text=text):
                reset_arities()
                formula = parse(text)
                reset_arities()
                self.assertEqual(parse(str(formula)), formula)

    def test_parse_matches_hand_built_formulae(self):
        self.assertEqual(
            parse("Ax(Fx -> Ey Rxy)"),
            Forall(
                self.x,
                Implies(Atom("F", self.x), Exists(self.y, Atom("R", self.x, self.y))),
            ),
        )

    def test_formula_parse_classmethod(self):
        from nd.formula import Formula

        self.assertEqual(Formula.parse("P & Q"), And(Atom("P"), Atom("Q")))


class TestUnicodeInput(ParserTestCase):
    def test_book_symbols_are_accepted(self):
        self.assertEqual(parse("¬P ∧ Q"), And(Not(Atom("P")), Atom("Q")))
        self.assertEqual(parse("P ∨ Q → S"), Implies(Or(Atom("P"), Atom("Q")), Atom("S")))
        self.assertEqual(parse("P ↔ Q"), Iff(Atom("P"), Atom("Q")))

    def test_printer_spacing_is_accepted(self):
        # The printer omits the space in these three forms.
        self.assertEqual(
            parse("∀x∃y Rxy"),
            Forall(self.x, Exists(self.y, Atom("R", self.x, self.y))),
        )
        self.assertEqual(parse("∀x¬Fx"), Forall(self.x, Not(Atom("F", self.x))))
        self.assertEqual(
            parse("∀x(Fx → Gx)"),
            Forall(self.x, Implies(Atom("F", self.x), Atom("G", self.x))),
        )

    def test_ascii_and_unicode_agree(self):
        self.assertEqual(parse("Ax(Fx -> Gx)"), parse("∀x(Fx → Gx)"))
        self.assertEqual(parse("~P"), parse("¬P"))


class TestLetters(ParserTestCase):
    def test_late_letters_are_variables(self):
        self.assertEqual(parse("Fx"), Atom("F", Variable("x")))
        self.assertEqual(parse("Fu"), Atom("F", Variable("u")))
        self.assertEqual(parse("Fz"), Atom("F", Variable("z")))

    def test_early_letters_are_constants(self):
        self.assertEqual(parse("Fa"), Atom("F", Constant("a")))
        self.assertEqual(parse("Ft"), Atom("F", Constant("t")))

    def test_variables_make_a_formula_open(self):
        self.assertFalse(parse("Fx").is_sentence())
        self.assertTrue(parse("Fa").is_sentence())
        self.assertTrue(parse("Ax Fx").is_sentence())

    def test_subscripts(self):
        self.assertEqual(parse("F_1x_2"), Atom("F_1", Variable("x_2")))
        self.assertEqual(parse("Fa_12"), Atom("F", Constant("a_12")))
        self.assertEqual(parse("Ax_1 Fx_1"), Forall(Variable("x_1"), Atom("F", Variable("x_1"))))

    def test_quantifying_a_constant_is_refused(self):
        self.assertParseError("Ab Fb", "constant letter", "cannot be quantified")

    def test_subscript_needs_an_underscore(self):
        self.assertParseError("F1x", "underscore")


class TestAtomForms(ParserTestCase):
    def test_juxtaposition_and_brackets_agree(self):
        self.assertEqual(parse("Rxy"), parse("R(x, y)"))
        self.assertEqual(parse("Fa"), parse("F(a)"))

    def test_sentence_letters_have_arity_zero(self):
        self.assertEqual(parse("P").arity, 0)
        self.assertEqual(parse("P()").arity, 0)

    def test_multi_letter_names_need_brackets(self):
        formula = parse("Loves(a, b)")
        self.assertEqual(formula, Atom("Loves", self.a, self.b))
        # Printed back in the bracketed form, since juxtaposition would
        # run the name into its terms.
        self.assertEqual(str(formula), "Loves(a, b)")

    def test_reserved_quantifier_letters_are_available_in_brackets(self):
        self.assertEqual(parse("A(x)"), Atom("A", self.x))
        self.assertEqual(str(parse("A(x)")), "A(x)")
        self.assertEqual(parse("A_1x"), Atom("A_1", self.x))

    def test_bare_A_is_the_quantifier_not_a_predicate(self):
        self.assertEqual(parse("Ax Fx"), Forall(self.x, Atom("F", self.x)))

    def test_no_function_symbols(self):
        self.assertParseError("f(x)", "no function symbols")


class TestPrecedence(ParserTestCase):
    def test_negation_binds_tightest(self):
        self.assertEqual(parse("~P & Q"), And(Not(Atom("P")), Atom("Q")))
        self.assertEqual(parse("~(P & Q)"), Not(And(Atom("P"), Atom("Q"))))

    def test_conjunction_binds_tighter_than_disjunction(self):
        self.assertEqual(
            parse("P & Q | S"), Or(And(Atom("P"), Atom("Q")), Atom("S"))
        )
        self.assertEqual(
            parse("P | Q & S"), Or(Atom("P"), And(Atom("Q"), Atom("S")))
        )

    def test_disjunction_binds_tighter_than_the_arrows(self):
        self.assertEqual(
            parse("P | Q -> S"), Implies(Or(Atom("P"), Atom("Q")), Atom("S"))
        )

    def test_binary_connectives_are_right_associative(self):
        p, q, s = Atom("P"), Atom("Q"), Atom("S")
        self.assertEqual(parse("P -> Q -> S"), Implies(p, Implies(q, s)))
        self.assertEqual(parse("P & Q & S"), And(p, And(q, s)))
        self.assertEqual(parse("P | Q | S"), Or(p, Or(q, s)))

    def test_quantifiers_take_the_smallest_scope(self):
        self.assertEqual(
            parse("Ax Fx -> Gx"),
            Implies(Forall(self.x, Atom("F", self.x)), Atom("G", self.x)),
        )
        self.assertEqual(
            parse("Ax(Fx -> Gx)"),
            Forall(self.x, Implies(Atom("F", self.x), Atom("G", self.x))),
        )

    def test_negation_and_quantifiers_nest_either_way(self):
        self.assertEqual(parse("~Ax Fx"), Not(Forall(self.x, Atom("F", self.x))))
        self.assertEqual(parse("Ax ~Fx"), Forall(self.x, Not(Atom("F", self.x))))

    def test_equality_binds_tighter_than_negation(self):
        self.assertEqual(parse("~a=b"), Not(Equality(self.a, self.b)))


class TestArrowMixing(ParserTestCase):
    def test_unbracketed_mixing_is_refused(self):
        self.assertParseError("P -> Q <-> S", "needs brackets")
        self.assertParseError("P <-> Q -> S", "needs brackets")

    def test_brackets_resolve_it(self):
        p, q, s = Atom("P"), Atom("Q"), Atom("S")
        self.assertEqual(parse("P -> (Q <-> S)"), Implies(p, Iff(q, s)))
        self.assertEqual(parse("(P -> Q) <-> S"), Iff(Implies(p, q), s))

    def test_repeating_one_arrow_is_fine(self):
        p, q, s = Atom("P"), Atom("Q"), Atom("S")
        self.assertEqual(parse("P -> Q -> S"), Implies(p, Implies(q, s)))
        self.assertEqual(parse("P <-> Q <-> S"), Iff(p, Iff(q, s)))

    def test_the_error_points_at_the_second_arrow(self):
        error = self.assertParseError("P -> Q <-> S", "needs brackets")
        self.assertEqual(error.position, 7)


class TestErrors(ParserTestCase):
    def test_empty_input(self):
        self.assertParseError("", "empty")
        self.assertParseError("   ", "empty")

    def test_unclosed_bracket(self):
        self.assertParseError("(P & Q", "')'")

    def test_trailing_input(self):
        self.assertParseError("P Q", "unexpected")

    def test_missing_operand(self):
        self.assertParseError("P &", "end of the input")
        self.assertParseError("& P", "expected a formula")

    def test_bare_v_is_not_disjunction(self):
        self.assertParseError("P v Q", "not disjunction", "'|'")

    def test_unknown_character(self):
        self.assertParseError("P # Q", "unexpected character")

    def test_quantifier_without_a_variable(self):
        self.assertParseError("Ax", "end of the input")
        self.assertParseError("A & P", "expected a variable", "A(x)")

    def test_error_reports_position_with_a_caret(self):
        error = self.assertParseError("P & & Q")
        self.assertEqual(error.position, 4)
        lines = str(error).splitlines()
        self.assertEqual(lines[-2], "  P & & Q")
        self.assertEqual(lines[-1], "  " + " " * 4 + "^")

    def test_arity_mismatch_surfaces(self):
        with self.assertRaises(ArityError):
            parse("Fx & Fxy")


class TestParseTerm(ParserTestCase):
    def test_variables_and_constants(self):
        self.assertEqual(parse_term("x"), Variable("x"))
        self.assertEqual(parse_term("a"), Constant("a"))
        self.assertEqual(parse_term("x_1"), Variable("x_1"))

    def test_rejects_a_formula(self):
        self.assertRaises(ParseError, parse_term, "Fx")
        self.assertRaises(ParseError, parse_term, "")

    def test_rejects_trailing_input(self):
        self.assertRaises(ParseError, parse_term, "x y")


class TestUsedWithTheRules(ParserTestCase):
    """The operations the deduction layer will call, driven from strings."""

    def test_universal_elimination(self):
        premise = parse("Ax(Fx -> Gx)")
        self.assertEqual(
            premise.body.substitute(self.x, self.a), parse("Fa -> Ga")
        )

    def test_universal_introduction(self):
        self.assertEqual(
            parse("Fa -> Ga").generalise(self.a, self.x), parse("Ax(Fx -> Gx)")
        )

    def test_capture_is_still_refused(self):
        from nd.formula import CaptureError

        with self.assertRaises(CaptureError):
            parse("Ey ~x=y").substitute(self.x, self.y)


if __name__ == "__main__":
    unittest.main()
