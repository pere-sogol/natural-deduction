"""Tests for ndweb.shadow: drawing a proof that is not finished.

``nd.render.layout`` reads six members and never asks whether it has a
``Proof``, so the same painter draws a derivation with holes in it.  That
is worth a test in both directions: a finished derivation must draw
exactly as its proof does, and an unfinished one must draw at all.
"""

import textwrap
import unittest

from nd.formula import reset_arities
from nd.parser import parse
from nd.render import layout, to_text

from ndweb.derivation import Binding, Goal, Step, substitute_node
from ndweb.exercises import EXERCISES, Builder, solution
from ndweb.realise import realise
from ndweb.shadow import Unknown, shadow


class TestFinishedDerivations(unittest.TestCase):
    def test_a_realised_derivation_draws_exactly_as_its_proof_does(self):
        """The student watches the book's own renderer, not a copy of it."""
        for exercise in EXERCISES:
            reset_arities()
            root = solution(exercise.key)
            realisation = realise(root)
            self.assertEqual(
                to_text(shadow(root, realisation)),
                to_text(realisation.proof),
                exercise.key,
            )

    def test_placement_agrees_too_not_merely_the_characters(self):
        reset_arities()
        root = solution("distribute")
        realisation = realise(root)
        drawn = layout(shadow(root, realisation))
        expected = layout(realisation.proof)
        self.assertEqual((drawn.width, drawn.height),
                         (expected.width, expected.height))
        self.assertEqual([f.text for f in drawn.formulae],
                         [f.text for f in expected.formulae])


class TestHoles(unittest.TestCase):
    def setUp(self):
        reset_arities()
        self.builder = Builder()

    def test_a_goal_draws_as_its_target_with_a_question_mark(self):
        """A backward step knows its target, so the bar below reads."""
        goal = Goal(1, parse("P & Q"))
        step = Step(2, "→Intro", (goal,), (Binding("assumption", parse("Q")),),
                    claim=parse("Q -> (P & Q)"))
        self.assertEqual(
            to_text(shadow(step, realise(step))),
            textwrap.dedent(
                """
                  P ∧ Q  ?
                ───────── →I
                Q → P ∧ Q
                """
            ).strip("\n"),
        )

    def test_a_blank_goal_is_never_bracketed_as_discharged(self):
        """It rests on nothing yet, so calling it closed would be false."""
        goal = Goal(3)
        step = Step(4, "→Intro", (goal,), (Binding("assumption", parse("P")),))
        drawn = to_text(shadow(step, realise(step)))
        self.assertNotIn("[", drawn)
        self.assertIn("?", drawn)

    def test_a_goal_written_into_is_bracketed_when_it_is_discharged(self):
        """A sentence at the top of a step, above nothing, is assumed.

        So the slot rests on itself and the step below closes it, exactly
        as it would an ``Assumption`` block -- and the student watches the
        discharge happen as they type rather than after they tidy up.
        """
        goal = Goal(3, parse("P"))
        step = Step(4, "→Intro", (goal,), (Binding("assumption", parse("P")),))
        drawn = to_text(shadow(step, realise(step)))
        self.assertIn("[P]¹", drawn)
        self.assertIn("?", drawn)

    def test_a_step_with_nothing_known_yet_draws_a_placeholder(self):
        step = Step(5, "∧Intro", (Goal(6, parse("P")), Goal(7, parse("Q"))))
        drawn = to_text(shadow(step, realise(step)))
        self.assertIn("?", drawn)

    def test_a_backward_step_shows_the_target_it_was_built_for(self):
        """With a claim there is something to write, even with holes above."""
        step = Step(8, "∧Intro", (Goal(9, parse("P")), Goal(10, parse("Q"))),
                    (), claim=parse("P & Q"))
        self.assertIn("P ∧ Q", to_text(shadow(step, realise(step))))

    def test_half_a_proof_still_draws_the_half_that_works(self):
        reset_arities()
        root = solution("russell")
        holed = substitute_node(root, 4, Goal(4, parse("Raa")))
        drawn = to_text(shadow(holed, realise(holed)))
        self.assertIn("∃x∀y(Rxy ↔ ¬Ryy)", drawn)
        # The hole keeps its ``?`` beside whatever is known of it -- here a
        # sentence a step below goes on to discharge, so it is bracketed.
        self.assertIn("[Raa]¹  ?", drawn)


class TestUnknown(unittest.TestCase):
    def test_it_prints_as_a_question_mark_and_matches_only_itself(self):
        first, second = Unknown(), Unknown()
        self.assertEqual(str(first), "?")
        self.assertNotEqual(first, second)
        self.assertEqual(first, first)
        self.assertNotEqual(first, parse("P"))
