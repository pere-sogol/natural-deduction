"""Tests for ndweb.refine, the backward reading of the rules.

The round-trip suite is the important one: for each rule, refine a goal,
prove the subgoals in the cheapest way available, and check that the
engine hands the goal back.  Refinement duplicates knowledge held in
``nd.rules`` -- this is what stops the two drifting apart, in the same way
that ``parse(str(f)) == f`` keeps the printer and the parser together.
"""

import unittest

from nd.formula import Constant, reset_arities
from nd.parser import parse
from nd.proofs import ProvisoError, rule_catalogue

from ndweb.derivation import Step
from ndweb.exercises import Builder
from ndweb.realise import realise
from ndweb.refine import BACKWARD, Context, RefineError, fields, probe, refine

#: A goal for each rule, with whatever the student would have to supply.
CASES = {
    "Assumption": ("P", {}),
    "=Intro": ("a=a", {}),
    "∧Intro": ("P & Q", {}),
    "∧Elim1": ("P", {"right": "Q"}),
    "∧Elim2": ("P", {"left": "Q"}),
    "∨Intro1": ("P | Q", {}),
    "∨Intro2": ("P | Q", {}),
    "∨Elim": ("S", {"disjunction": "P | Q"}),
    "→Intro": ("P -> Q", {}),
    "→Elim": ("Q", {"antecedent": "P"}),
    "¬Intro": ("~P", {"witness": "Q"}),
    "¬Elim": ("P", {"witness": "Q"}),
    "↔Intro": ("P <-> Q", {}),
    "↔Elim1": ("Q", {"other": "P"}),
    "↔Elim2": ("P", {"other": "Q"}),
    "∀Intro": ("Ax x=x", {"constant": "a"}),
    "∀Elim": ("Fa", {"universal": "Ax Fx"}),
    "∃Intro": ("Ex Fx", {"constant": "a"}),
    "∃Elim": ("P", {"existential": "Ex Fx", "constant": "a"}),
    "=Elim1": ("Rbb", {"identity": "a=b"}),
    "=Elim2": ("Raa", {"identity": "a=b"}),
}

#: Subgoals some rules cannot have closed by a bare assumption.  ``AIntro``
#: is the case: assuming its instance leaves the parameter occurring in an
#: open assumption, so the arbitrariness proviso refuses -- the filler is at
#: fault, not the refinement.
FILLERS = {"∀Intro": lambda builder, target: builder.step(
    "=Intro", constant=Constant("a"))}


class RefineTestCase(unittest.TestCase):
    def setUp(self):
        reset_arities()


class TestRoundTrip(RefineTestCase):
    def test_every_rule_gives_its_goal_back(self):
        for name, (text, inputs) in CASES.items():
            reset_arities()
            target = parse(text)
            refinement = refine(
                name, target, Context(available=frozenset({target})), inputs
            )
            builder = Builder(100)
            filler = FILLERS.get(name)
            children = tuple(
                filler(builder, subgoal.target) if filler
                else builder.assume(subgoal.target)
                for subgoal in refinement.subgoals
            )
            step = Step(1, name, children, refinement.params, target)
            realisation = realise(step)

            if realisation.complete:
                self.assertEqual(realisation.proof.conclusion, target, name)
            else:
                # A proviso may still bite, because closing a subgoal with a
                # bare assumption can leave a parameter where it may not be.
                # Anything else means the refinement got the logic wrong.
                failure = realisation.failures[1]
                self.assertEqual(failure.kind, "proviso", "{0}: {1}".format(
                    name, failure.message))

    def test_the_table_covers_the_catalogue_exactly(self):
        self.assertEqual(
            sorted(BACKWARD), sorted(cls.name for cls in rule_catalogue())
        )
        self.assertEqual(sorted(CASES), sorted(BACKWARD))


class TestShapeGating(RefineTestCase):
    def test_an_introduction_refuses_a_goal_of_the_wrong_shape(self):
        for name, wrong in (
            ("∧Intro", "P | Q"), ("∨Intro1", "P & Q"), ("→Intro", "P & Q"),
            ("↔Intro", "P -> Q"), ("¬Intro", "P"), ("∀Intro", "Ex Fx"),
            ("∃Intro", "Ax Fx"), ("=Intro", "P"),
        ):
            reset_arities()
            with self.assertRaises(RefineError, msg=name):
                refine(name, parse(wrong), Context(), {})

    def test_identity_introduction_needs_both_sides_the_same(self):
        with self.assertRaises(RefineError) as caught:
            refine("=Intro", parse("a=b"), Context(), {})
        self.assertIn("itself", caught.exception.message)

    def test_an_elimination_will_try_any_goal(self):
        """They are how you get at what you have, so nothing gates them."""
        for name in ("∧Elim1", "→Elim", "¬Elim", "∨Elim"):
            self.assertIsInstance(fields(name, parse("P & Q"), Context()), tuple)


class TestQuantifierProvisos(RefineTestCase):
    def test_generalising_refuses_a_parameter_already_in_the_goal(self):
        """Ax Rxa at c = a would reach Ax Rxx, which is a different sentence."""
        with self.assertRaises(RefineError) as caught:
            refine("∀Intro", parse("Ax Rxa"), Context(), {"constant": "a"})
        self.assertIn("already occurs", caught.exception.message)

    def test_the_suggested_parameter_avoids_the_goal(self):
        wanted = fields("∀Intro", parse("Ax Rxa"), Context())[0]
        self.assertEqual(wanted.default, "a_1")

    def test_a_good_parameter_generalises_back_to_the_goal(self):
        target = parse("Ax Rxa")
        refinement = refine("∀Intro", target, Context(), {"constant": "b"})
        subgoal = refinement.subgoals[0].target
        self.assertEqual(subgoal, parse("Rba"))
        self.assertEqual(
            subgoal.generalise(Constant("b"), target.variable), target
        )

    def test_arbitrariness_only_warns_because_it_may_yet_be_discharged(self):
        context = Context(available=frozenset({parse("Fa")}))
        refinement = refine("∀Intro", parse("Ax Gx"), context, {"constant": "a"})
        self.assertTrue(refinement.warnings)
        self.assertIn("arbitrary", refinement.warnings[0])

    def test_existential_elimination_refuses_an_unfresh_parameter(self):
        for inputs, where in (
            ({"existential": "Ex Rxa", "constant": "a"}, "the existential"),
            ({"existential": "Ex Fx", "constant": "b"}, "the goal"),
        ):
            reset_arities()
            with self.assertRaises(RefineError) as caught:
                refine("∃Elim", parse("Gb"), Context(), inputs)
            self.assertIn(where, caught.exception.message)

    def test_existential_elimination_suggests_a_fresh_parameter(self):
        wanted = dict(
            (f.name, f) for f in fields("∃Elim", parse("Ga"), Context())
        )
        self.assertEqual(wanted["constant"].default, "a_1")

    def test_a_vacuous_existential_asks_for_no_parameter(self):
        """Ex P binds nothing, so there is no witness to name."""
        self.assertEqual(fields("∃Intro", parse("Ex P"), Context()), ())
        refinement = refine("∃Intro", parse("Ex P"), Context(), {})
        self.assertEqual(refinement.subgoals[0].target, parse("P"))
        self.assertEqual([b.name for b in refinement.params], ["conclusion"])


class TestUniversalElimination(RefineTestCase):
    def test_it_finds_the_constant_rather_than_asking_for_it(self):
        refinement = refine(
            "∀Elim", parse("Fa -> Ga"), Context(),
            {"universal": "Ax(Fx -> Gx)"},
        )
        self.assertEqual(
            [b.value for b in refinement.params if b.name == "constant"],
            [Constant("a")],
        )

    def test_it_refuses_a_universal_that_does_not_instantiate_to_the_goal(self):
        with self.assertRaises(RefineError) as caught:
            refine("∀Elim", parse("Ga"), Context(), {"universal": "Ax Fx"})
        self.assertIn("no constant", caught.exception.message)


class TestIdentityElimination(RefineTestCase):
    def test_the_source_defaults_to_undoing_the_replacement(self):
        refinement = refine("=Elim1", parse("Rbb"), Context(),
                            {"identity": "a=b"})
        self.assertEqual(
            [str(s.target) for s in refinement.subgoals], ["a=b", "Raa"]
        )

    def test_the_other_direction_defaults_the_other_way(self):
        refinement = refine("=Elim2", parse("Raa"), Context(),
                            {"identity": "a=b"})
        self.assertEqual(
            [str(s.target) for s in refinement.subgoals], ["a=b", "Rbb"]
        )

    def test_a_source_may_be_given_instead(self):
        """Replacement is of some occurrences, so the default is only one."""
        refinement = refine("=Elim1", parse("Rbb"), Context(),
                            {"identity": "a=b", "source": "Rab"})
        self.assertEqual(refinement.subgoals[1].target, parse("Rab"))


class TestSuggestions(RefineTestCase):
    def test_a_conditional_in_scope_offers_its_antecedent(self):
        context = Context(available=frozenset({parse("P -> Q"), parse("S -> R")}))
        wanted = fields("→Elim", parse("Q"), context)[0]
        self.assertEqual(wanted.suggestions, ("P",))

    def test_a_disjunction_in_scope_is_offered_for_arguing_by_cases(self):
        context = Context(available=frozenset({parse("P | Q")}))
        self.assertEqual(
            fields("∨Elim", parse("S"), context)[0].suggestions, ("P ∨ Q",)
        )

    def test_nothing_in_scope_means_nothing_offered(self):
        self.assertEqual(fields("→Elim", parse("Q"), Context())[0].suggestions, ())


class TestAssumption(RefineTestCase):
    def test_it_closes_a_goal_that_is_available(self):
        target = parse("P")
        refinement = refine("Assumption", target,
                            Context(available=frozenset({target})), {})
        self.assertEqual(refinement.subgoals, ())
        self.assertEqual(refinement.warnings, ())

    def test_it_warns_rather_than_refuses_when_it_is_not(self):
        """Assuming something new is allowed; it just stays open."""
        refinement = refine("Assumption", parse("P"), Context(), {})
        self.assertTrue(refinement.warnings)
        self.assertIn("stay open", refinement.warnings[0])


class TestMissingInput(RefineTestCase):
    def test_a_rule_wanting_a_formula_says_so_rather_than_guessing(self):
        with self.assertRaises(RefineError) as caught:
            refine("→Elim", parse("Q"), Context(), {})
        self.assertIn("antecedent", caught.exception.message)

    def test_unparseable_input_reports_where_it_stopped(self):
        with self.assertRaises(RefineError) as caught:
            refine("→Elim", parse("Q"), Context(), {"antecedent": "P ->"})
        self.assertIn("column", caught.exception.message)

    def test_a_variable_where_a_constant_belongs_is_refused(self):
        with self.assertRaises(RefineError) as caught:
            refine("∀Intro", parse("Ax Fx"), Context(), {"constant": "x"})
        self.assertIn("variable", caught.exception.message)


class TestProbe(RefineTestCase):
    def test_it_reports_every_rule_with_a_reason_when_unavailable(self):
        found = dict((p.rule, p) for p in probe(parse("P & Q"), Context()))
        self.assertEqual(len(found), 21)
        self.assertTrue(found["∧Intro"].available)
        self.assertFalse(found["∨Intro1"].available)
        self.assertIn("disjunction", found["∨Intro1"].reason)

    def test_classical_negation_is_offered_for_any_goal(self):
        """It is how excluded middle is reached, so it must never be hidden."""
        for text in ("P", "P & Q", "Ax Fx", "a=b"):
            reset_arities()
            found = dict((p.rule, p) for p in probe(parse(text), Context()))
            self.assertTrue(found["¬Elim"].available, text)

    def test_what_a_rule_wants_comes_back_with_it(self):
        found = dict((p.rule, p) for p in probe(parse("Q"), Context()))
        self.assertEqual([f.name for f in found["→Elim"].wants], ["antecedent"])
