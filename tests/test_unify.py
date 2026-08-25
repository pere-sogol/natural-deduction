"""Tests for ndweb.unify: what a half-filled block settles about itself.

The property worth having is that neither direction invents anything.
Downwards is the engine applied to the premises as they stand, so it is
checked against ``realise`` on the corpus; upwards is the refinement
table, so it is checked by writing the conclusion of a recorded proof into
a bare block and seeing the premises come back.
"""

import unittest

from nd.formula import Constant, Variable, reset_arities
from nd.parser import parse
from nd.proofs import rule_catalogue

from ndweb.derivation import Binding, Goal, Step, walk
from ndweb.exercises import EXERCISES, solution
from ndweb.realise import realise
from ndweb.unify import FROM_PREMISE, MIRRORS, predict, solve


class UnifyTestCase(unittest.TestCase):
    def setUp(self):
        reset_arities()

    def block(self, rule, premises=(), params=(), claim=None):
        """One rule with the given slots written in, the rest blank."""
        children = tuple(
            Goal(index + 1, None if text is None else parse(text))
            for index, text in enumerate(premises)
        )
        return Step(0, rule, children, tuple(params),
                    None if claim is None else parse(claim))

    def solved(self, *args, **kwargs):
        found = solve(self.block(*args, **kwargs))
        return dict((key, str(value)) for key, value in found.formulas.items())


class TestDownwards(UnifyTestCase):
    def test_the_premises_give_the_conclusion(self):
        self.assertEqual(self.solved("∧Intro", ("P", "Q"))[0], "P ∧ Q")

    def test_it_is_the_engine_answering_not_a_second_table(self):
        """predict stands the premises up as assumptions and applies the rule."""
        conclusion, failure = predict("∧Elim1", [parse("P & Q")], {})
        self.assertEqual(str(conclusion), "P")
        self.assertIsNone(failure)

    def test_a_rule_that_does_not_apply_says_so_rather_than_guessing(self):
        conclusion, failure = predict("∧Elim1", [parse("P")], {})
        self.assertIsNone(conclusion)
        self.assertEqual(failure.kind, "shape")

    def test_the_major_premise_alone_settles_an_elimination(self):
        """→Elim given its conditional knows both the rest and the answer."""
        found = self.solved("→Elim", (None, "P -> Q"))
        self.assertEqual((found[0], found[1]), ("Q", "P"))

    def test_the_bound_variable_of_a_generalisation_is_not_worth_asking_for(self):
        found = solve(self.block(
            "∀Intro", ("Fa",), (Binding("constant", Constant("a")),)))
        self.assertEqual(str(found.formulas[0]), "∀x Fx")
        self.assertEqual(found.params[0]["variable"], Variable("x"))

    def test_it_avoids_a_variable_already_bound_in_the_premise(self):
        found = solve(self.block(
            "∀Intro", ("Ax Rxa",), (Binding("constant", Constant("a")),)))
        self.assertEqual(str(found.formulas[0]), "∀y∀x Rxy")

    def test_an_unsettled_proviso_predicts_but_does_not_prove(self):
        """Whether c stays arbitrary depends on branches not yet built.

        Showing nothing until the block is finished would leave it blank
        for as long as it took to build, so the conclusion is predicted --
        and realise still applies the rule for real, and still refuses.
        """
        block = Step(
            0, "∀Intro",
            (Step(1, "Assumption", (), (), parse("Fa")),),
            (Binding("constant", Constant("a")), Binding("variable", Variable("x"))),
        )
        self.assertEqual(str(solve(block).formulas[0]), "∀x Fx")
        self.assertIsNone(realise(block).proof)
        self.assertEqual(realise(block).failures[0].kind, "proviso")
        self.assertIn("not arbitrary", realise(block).failures[0].message)


class TestUpwards(UnifyTestCase):
    def test_the_conclusion_gives_the_premises(self):
        found = self.solved("∧Intro", (None, None), claim="P & Q")
        self.assertEqual((found[1], found[2]), ("P", "Q"))

    def test_a_premise_answers_what_refinement_would_have_asked(self):
        """→Elim's antecedent is a premise slot, not a question."""
        found = self.solved("→Elim", ("P", None), claim="Q")
        self.assertEqual(found[2], "P → Q")

    def test_every_rule_that_reads_a_field_off_a_premise_has_that_premise(self):
        arities = dict((cls.name, cls.subproof_count) for cls in rule_catalogue())
        for name, mapping in FROM_PREMISE.items():
            for field, index in mapping.items():
                self.assertLess(index, arities[name],
                                "{0}.{1} points past its premises".format(name, field))

    def test_a_premise_that_repeats_the_conclusion_is_filled_at_once(self):
        """Both cases of ∨Elim argue for the goal, whatever the disjunction."""
        found = self.solved("∨Elim", (None, None, None), claim="R")
        self.assertEqual((found[1], found[2]), ("R", "R"))
        self.assertNotIn(3, found)

    def test_the_mirrors_are_the_ones_the_figures_show(self):
        """The palette draws these rules; the two must not come apart."""
        from ndweb.catalogue import SCHEMA

        for name, (premises, conclusion, _) in SCHEMA.items():
            shown = tuple(
                index for index, text in enumerate(premises) if text == conclusion
            )
            self.assertEqual(MIRRORS.get(name, ()), shown, name)

    def test_a_parameter_the_conclusion_settles_is_filled_in(self):
        found = solve(self.block("→Intro", (None,), claim="P -> Q"))
        self.assertEqual(found.params[0]["assumption"], parse("P"))

    def test_a_rule_that_cannot_reach_the_goal_leaves_a_note_not_a_guess(self):
        found = solve(self.block("∧Intro", (None, None), claim="P -> Q"))
        self.assertNotIn(1, found.formulas)
        self.assertIn("conjunction", found.notes[0][0])


class TestTheTwoTogether(UnifyTestCase):
    def test_the_directions_agree_on_every_recorded_proof(self):
        """Solving a proof's own tree must say what realising it says."""
        for exercise in EXERCISES:
            reset_arities()
            root = solution(exercise.key)
            found = solve(root)
            realisation = realise(root, found)
            for node in walk(root):
                self.assertEqual(
                    found.formula(node.id),
                    realisation.conclusion(node.id),
                    "{0}: node {1}".format(exercise.key, node.id),
                )

    def test_writing_the_conclusion_reaches_what_the_premises_would(self):
        forwards = self.solved("∧Intro", ("P", "Q"))
        backwards = self.solved("∧Intro", (None, None), claim="P & Q")
        self.assertEqual(forwards, backwards)

    def test_what_the_conclusion_cannot_settle_is_left_alone(self):
        """↔Elim1 concluding ψ says nothing about which φ it came through.

        Nothing is invented for it: the premise stays an empty slot, and a
        student writes the biconditional in when they know it.
        """
        found = solve(self.block("↔Elim1", (None, None), claim="Q"))
        self.assertNotIn(1, found.formulas)
        self.assertNotIn(2, found.formulas)

    def test_what_was_written_is_recorded_apart_from_what_was_worked_out(self):
        found = solve(self.block("∧Intro", (None, None), claim="P & Q"))
        self.assertTrue(found.is_written(0))
        self.assertFalse(found.is_written(1))


class TestScope(UnifyTestCase):
    def test_a_discharging_step_widens_what_is_available_above_it(self):
        found = solve(self.block("→Intro", (None,), claim="P -> Q"))
        self.assertEqual(found.available[1], frozenset({parse("P")}))

    def test_the_premises_of_the_sequent_reach_everywhere(self):
        found = solve(self.block("∧Intro", (None, None), claim="P & Q"),
                      frozenset({parse("S")}))
        self.assertIn(parse("S"), found.available[1])
        self.assertIn(parse("S"), found.available[2])
