"""Tests for the language layer, nd.formula."""

import unittest

from nd.formula import (
    And,
    ArityError,
    Atom,
    CaptureError,
    Constant,
    Equality,
    Exists,
    Forall,
    Iff,
    Implies,
    Not,
    Or,
    Variable,
    fresh_constant,
    fresh_variable,
    reset_arities,
)


class FormulaTestCase(unittest.TestCase):
    """Shared fixtures.

    Predicate arities live in module-level state, so every case starts
    from a clean registry.
    """

    def setUp(self):
        reset_arities()
        self.x = Variable("x")
        self.y = Variable("y")
        self.z = Variable("z")
        self.a = Constant("a")
        self.b = Constant("b")

    def Fx(self):
        return Atom("F", self.x)

    def Gx(self):
        return Atom("G", self.x)


class TestVariables(FormulaTestCase):
    def test_quantifier_binds_its_variable(self):
        formula = Forall(self.x, Implies(self.Fx(), Exists(self.y, Atom("R", self.x, self.y))))
        self.assertEqual(formula.free_variables(), frozenset())
        self.assertEqual(formula.bound_variables(), frozenset({self.x, self.y}))

    def test_open_formula_reports_its_free_variable(self):
        formula = Implies(self.Fx(), Exists(self.y, Atom("R", self.x, self.y)))
        self.assertEqual(formula.free_variables(), frozenset({self.x}))
        self.assertEqual(formula.bound_variables(), frozenset({self.y}))

    def test_variable_free_in_one_conjunct_bound_in_the_other(self):
        # In 'Fx & Ax Gx' the same letter is free on the left, bound on
        # the right, and must show up in both sets.
        formula = And(self.Fx(), Forall(self.x, self.Gx()))
        self.assertEqual(formula.free_variables(), frozenset({self.x}))
        self.assertEqual(formula.bound_variables(), frozenset({self.x}))
        self.assertEqual(formula.variables(), frozenset({self.x}))

    def test_is_sentence(self):
        self.assertTrue(Forall(self.x, self.Fx()).is_sentence())
        self.assertTrue(Atom("F", self.a).is_sentence())
        self.assertFalse(self.Fx().is_sentence())

    def test_constants_and_predicates(self):
        formula = And(Atom("R", self.a, self.b), Forall(self.x, Atom("F", self.x)))
        self.assertEqual(formula.constants(), frozenset({self.a, self.b}))
        self.assertEqual(formula.predicates(), frozenset({("R", 2), ("F", 1)}))

    def test_sentence_letter_has_no_terms(self):
        p = Atom("P")
        self.assertEqual(p.arity, 0)
        self.assertEqual(p.free_variables(), frozenset())
        self.assertEqual(p.constants(), frozenset())

    def test_equality_reports_its_terms(self):
        formula = Exists(self.y, Not(Equality(self.x, self.y)))
        self.assertEqual(formula.free_variables(), frozenset({self.x}))
        self.assertEqual(Equality(self.a, self.b).constants(), frozenset({self.a, self.b}))

    def test_subformulas(self):
        formula = Forall(self.x, Implies(self.Fx(), self.Gx()))
        self.assertEqual(
            list(formula.subformulas()),
            [formula, formula.body, self.Fx(), self.Gx()],
        )


class TestSubstitution(FormulaTestCase):
    def test_universal_elimination(self):
        formula = Forall(self.x, Implies(self.Fx(), self.Gx()))
        instance = formula.body.substitute(self.x, self.a)
        self.assertEqual(instance, Implies(Atom("F", self.a), Atom("G", self.a)))

    def test_substitution_reaches_only_free_occurrences(self):
        # The bound 'x' on the right must be left alone.
        formula = And(self.Fx(), Forall(self.x, self.Gx()))
        self.assertEqual(
            formula.substitute(self.x, self.a),
            And(Atom("F", self.a), Forall(self.x, self.Gx())),
        )

    def test_substituting_a_variable_not_free_changes_nothing(self):
        formula = Forall(self.x, self.Fx())
        self.assertEqual(formula.substitute(self.x, self.a), formula)
        self.assertEqual(formula.substitute(self.y, self.a), formula)

    def test_substitution_into_equality(self):
        formula = Equality(self.x, self.y)
        self.assertEqual(
            formula.substitute(self.x, self.a), Equality(self.a, self.y)
        )


class TestCapture(FormulaTestCase):
    def test_capture_is_refused(self):
        # Substituting y for x in 'Ey ~x=y' would turn a claim that
        # something differs from x into the falsehood 'Ey ~y=y'.
        formula = Exists(self.y, Not(Equality(self.x, self.y)))
        self.assertFalse(formula.is_free_for(self.y, self.x))
        with self.assertRaises(CaptureError):
            formula.substitute(self.x, self.y)

    def test_free_for_when_nothing_is_captured(self):
        formula = Exists(self.y, Not(Equality(self.x, self.y)))
        self.assertTrue(formula.is_free_for(self.z, self.x))
        self.assertTrue(formula.is_free_for(self.a, self.x))
        self.assertEqual(
            formula.substitute(self.x, self.z),
            Exists(self.y, Not(Equality(self.z, self.y))),
        )

    def test_free_for_when_the_variable_is_not_free_there(self):
        # No free occurrence of x survives under 'Ax', so there is
        # nothing for the quantifier to capture.
        formula = Forall(self.x, Atom("R", self.x, self.y))
        self.assertTrue(formula.is_free_for(self.x, self.x))

    def test_quantifier_elsewhere_does_not_block_substitution(self):
        # The y introduced into the left conjunct stays free; the 'Ay' on
        # the right is not in its way.
        formula = And(self.Fx(), Forall(self.y, Atom("G", self.y)))
        self.assertTrue(formula.is_free_for(self.y, self.x))
        self.assertEqual(
            formula.substitute(self.x, self.y),
            And(Atom("F", self.y), Forall(self.y, Atom("G", self.y))),
        )

    def test_error_message_names_the_terms(self):
        formula = Exists(self.y, Not(Equality(self.x, self.y)))
        with self.assertRaises(CaptureError) as caught:
            formula.substitute(self.x, self.y)
        self.assertIn("y is not free for x", str(caught.exception))


class TestGeneralisation(FormulaTestCase):
    def test_universal_introduction(self):
        premise = Implies(Atom("F", self.a), Atom("G", self.a))
        self.assertEqual(
            premise.generalise(self.a, self.x),
            Forall(self.x, Implies(self.Fx(), self.Gx())),
        )

    def test_existential_introduction(self):
        premise = Atom("F", self.a)
        self.assertEqual(
            premise.generalise(self.a, self.x, "exists"),
            Exists(self.x, self.Fx()),
        )

    def test_generalising_then_instantiating_returns_the_premise(self):
        premise = Implies(Atom("F", self.a), Atom("G", self.a))
        generalised = premise.generalise(self.a, self.x)
        self.assertEqual(generalised.body.substitute(self.x, self.a), premise)

    def test_other_constants_are_untouched(self):
        premise = Atom("R", self.a, self.b)
        self.assertEqual(
            premise.generalise(self.a, self.x),
            Forall(self.x, Atom("R", self.x, self.b)),
        )

    def test_generalising_into_an_existing_binder_is_refused(self):
        # 'a' sits under 'Ax', so renaming it to x would capture it.
        premise = Forall(self.x, Atom("R", self.x, self.a))
        with self.assertRaises(CaptureError):
            premise.generalise(self.a, self.x)

    def test_unknown_quantifier_is_rejected(self):
        with self.assertRaises(ValueError):
            Atom("F", self.a).generalise(self.a, self.x, "some")

    def test_existential_introduction_on_some_occurrences_is_checked_not_generated(self):
        # From 'Raa' one may infer 'Ex Rxa' as well as 'Ex Rxx'.
        # generalise() only produces the replace-every reading, so the
        # partial one is verified by substituting back.
        premise = Atom("R", self.a, self.a)
        partial = Exists(self.x, Atom("R", self.x, self.a))
        self.assertEqual(partial.body.substitute(self.x, self.a), premise)
        self.assertEqual(
            premise.generalise(self.a, self.x, "exists"),
            Exists(self.x, Atom("R", self.x, self.x)),
        )


class TestReplaceTerm(FormulaTestCase):
    def test_identity_elimination(self):
        # From a=b and Fa, infer Fb.
        self.assertEqual(
            Atom("F", self.a).replace_term(self.a, self.b), Atom("F", self.b)
        )

    def test_replaces_every_free_occurrence(self):
        self.assertEqual(
            Atom("R", self.a, self.a).replace_term(self.a, self.b),
            Atom("R", self.b, self.b),
        )

    def test_capture_is_refused(self):
        formula = Forall(self.y, Atom("R", self.x, self.y))
        with self.assertRaises(CaptureError):
            formula.replace_term(self.x, self.y)


class TestArity(FormulaTestCase):
    def test_mismatched_arity_is_rejected(self):
        Atom("F", self.x)
        with self.assertRaises(ArityError):
            Atom("F", self.x, self.y)

    def test_consistent_use_is_accepted(self):
        Atom("R", self.x, self.y)
        Atom("R", self.a, self.b)

    def test_error_message_names_both_arities(self):
        Atom("F", self.x)
        with self.assertRaises(ArityError) as caught:
            Atom("F", self.x, self.y)
        message = str(caught.exception)
        self.assertIn("arity 2", message)
        self.assertIn("arity 1", message)

    def test_reset_clears_the_registry(self):
        Atom("F", self.x)
        reset_arities()
        Atom("F", self.x, self.y)  # no longer a clash


class TestEqualityAndHashing(FormulaTestCase):
    def test_structurally_identical_formulae_are_equal(self):
        first = Forall(self.x, Implies(self.Fx(), self.Gx()))
        second = Forall(self.x, Implies(self.Fx(), self.Gx()))
        self.assertEqual(first, second)
        self.assertEqual(hash(first), hash(second))
        self.assertEqual(len({first, second}), 1)

    def test_different_connectives_are_unequal(self):
        p, q = Atom("P"), Atom("Q")
        self.assertNotEqual(And(p, q), Or(p, q))
        self.assertNotEqual(Implies(p, q), Iff(p, q))

    def test_order_matters(self):
        p, q = Atom("P"), Atom("Q")
        self.assertNotEqual(Implies(p, q), Implies(q, p))

    def test_alpha_variants_are_unequal_but_alpha_equivalent(self):
        first = Forall(self.x, self.Fx())
        second = Forall(self.y, Atom("F", self.y))
        self.assertNotEqual(first, second)
        self.assertTrue(first.alpha_equivalent(second))

    def test_alpha_equivalence_respects_binding_structure(self):
        # 'Ax Ey Rxy' and 'Ax Ey Ryx' bind the same names differently.
        first = Forall(self.x, Exists(self.y, Atom("R", self.x, self.y)))
        second = Forall(self.x, Exists(self.y, Atom("R", self.y, self.x)))
        self.assertFalse(first.alpha_equivalent(second))

    def test_alpha_equivalence_does_not_confuse_free_variables(self):
        self.assertFalse(self.Fx().alpha_equivalent(Atom("F", self.y)))

    def test_alpha_equivalence_under_shadowing(self):
        # In 'Ax Ax Fx' the inner quantifier shadows the outer, so the
        # outer bound name is free to differ.
        first = Forall(self.x, Forall(self.x, self.Fx()))
        second = Forall(self.y, Forall(self.x, self.Fx()))
        self.assertTrue(first.alpha_equivalent(second))

    def test_alpha_equivalence_tracks_which_binder_is_which(self):
        first = Forall(self.x, Exists(self.y, Atom("R", self.x, self.y)))
        second = Forall(self.y, Exists(self.x, Atom("R", self.y, self.x)))
        self.assertTrue(first.alpha_equivalent(second))

    def test_formulae_are_immutable(self):
        with self.assertRaises(Exception):
            Atom("P").predicate = "Q"
        with self.assertRaises(Exception):
            Not(Atom("P")).sub = Atom("Q")

    def test_formulae_work_as_dictionary_keys(self):
        assumptions = {Atom("F", self.a): "premise"}
        self.assertEqual(assumptions[Atom("F", self.a)], "premise")


class TestConstruction(FormulaTestCase):
    def test_operators_match_the_named_constructors(self):
        p, q = Atom("P"), Atom("Q")
        self.assertEqual(~p, Not(p))
        self.assertEqual(p & q, And(p, q))
        self.assertEqual(p | q, Or(p, q))
        self.assertEqual(p.implies(q), Implies(p, q))
        self.assertEqual(p.iff(q), Iff(p, q))

    def test_operators_nest(self):
        p, q, r = Atom("P"), Atom("Q"), Atom("S")
        self.assertEqual((p & q).implies(~r), Implies(And(p, q), Not(r)))


class TestFreshNames(FormulaTestCase):
    def test_unused_stem_is_returned_unchanged(self):
        self.assertEqual(fresh_constant([self.b]), Constant("a"))
        self.assertEqual(fresh_variable([self.y]), Variable("x"))

    def test_used_stem_is_subscripted(self):
        self.assertEqual(fresh_constant([self.a]), Constant("a_1"))
        self.assertEqual(
            fresh_constant([self.a, Constant("a_1")]), Constant("a_2")
        )

    def test_fresh_constant_avoids_a_formulas_constants(self):
        formula = And(Atom("F", self.a), Atom("G", self.b))
        self.assertNotIn(fresh_constant(formula.constants()), formula.constants())

    def test_variables_and_constants_do_not_collide(self):
        # Only constants can rule out a constant name.
        self.assertEqual(fresh_constant([Variable("a")]), Constant("a"))


class TestPrinting(FormulaTestCase):
    def test_atoms_are_juxtaposed(self):
        self.assertEqual(str(Atom("F", self.x)), "Fx")
        self.assertEqual(str(Atom("R", self.x, self.y)), "Rxy")
        self.assertEqual(str(Atom("P")), "P")

    def test_identity_is_infix(self):
        self.assertEqual(str(Equality(self.a, self.b)), "a=b")
        self.assertEqual(str(Not(Equality(self.a, self.b))), "¬a=b")

    def test_no_brackets_where_precedence_settles_it(self):
        p, q, r = Atom("P"), Atom("Q"), Atom("S")
        self.assertEqual(str(And(p, q).implies(r)), "P ∧ Q → S")
        self.assertEqual(str(Or(And(p, q), r)), "P ∧ Q ∨ S")
        self.assertEqual(str(Not(p) & q), "¬P ∧ Q")

    def test_brackets_where_they_are_needed(self):
        p, q, r = Atom("P"), Atom("Q"), Atom("S")
        self.assertEqual(str(And(p, Implies(q, r))), "P ∧ (Q → S)")
        self.assertEqual(str(And(Or(p, q), r)), "(P ∨ Q) ∧ S")
        self.assertEqual(str(Not(Or(p, q))), "¬(P ∨ Q)")

    def test_arrows_are_right_associative(self):
        p, q, r = Atom("P"), Atom("Q"), Atom("S")
        self.assertEqual(str(Implies(p, Implies(q, r))), "P → Q → S")
        self.assertEqual(str(Implies(Implies(p, q), r)), "(P → Q) → S")

    def test_quantifiers_take_the_smallest_scope(self):
        wide = Forall(self.x, Implies(self.Fx(), self.Gx()))
        narrow = Implies(Forall(self.x, self.Fx()), Atom("G", self.a))
        self.assertEqual(str(wide), "∀x(Fx → Gx)")
        self.assertEqual(str(narrow), "∀x Fx → Ga")

    def test_space_after_the_variable_only_before_a_predicate_letter(self):
        formula = Forall(self.x, Exists(self.y, Atom("R", self.x, self.y)))
        self.assertEqual(str(formula), "∀x∃y Rxy")
        self.assertEqual(str(Forall(self.x, Not(self.Fx()))), "∀x¬Fx")
        self.assertEqual(str(Forall(self.x, self.Fx())), "∀x Fx")

    def test_printing_does_not_normalise_bound_names(self):
        first = Forall(self.x, self.Fx())
        second = Forall(self.y, Atom("F", self.y))
        self.assertTrue(first.alpha_equivalent(second))
        self.assertNotEqual(str(first), str(second))

    def test_repr_reconstructs_the_formula(self):
        formula = Forall(self.x, Implies(self.Fx(), self.Gx()))
        self.assertEqual(eval(repr(formula)), formula)  # noqa: S307


if __name__ == "__main__":
    unittest.main()
