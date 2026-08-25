"""Tests for ndweb.realise: checking a derivation, as far as it goes."""

import unittest

from nd.formula import Constant, Not, Variable, reset_arities
from nd.parser import parse

from ndweb.derivation import (
    Binding,
    Card,
    Document,
    Goal,
    Step,
    substitute_node,
)
from ndweb.exercises import EXERCISES, Builder, solution
from ndweb.realise import contexts, realise


class TestTheCorpus(unittest.TestCase):
    def test_every_recorded_solution_proves_its_sequent(self):
        for exercise in EXERCISES:
            reset_arities()
            realisation = realise(solution(exercise.key))
            self.assertTrue(realisation.complete, exercise.key)
            self.assertTrue(
                realisation.proof.proves(
                    parse(exercise.goal),
                    frozenset(parse(premise) for premise in exercise.premises),
                ),
                "{0}: got {1} resting on {2}".format(
                    exercise.key,
                    realisation.proof.conclusion,
                    sorted(str(f) for f in realisation.proof.assumptions),
                ),
            )
            self.assertEqual(realisation.failures, {})
            self.assertEqual(realisation.open_goals, ())


class RealiseTestCase(unittest.TestCase):
    def setUp(self):
        reset_arities()
        self.p, self.q = parse("P"), parse("Q")
        self.builder = Builder()


class TestPartialProofs(RealiseTestCase):
    def test_a_hole_is_reported_and_blocks_only_the_steps_below_it(self):
        """The rest of the tree is still drawn, and still checked."""
        reset_arities()
        root = solution("russell")
        whole = realise(root)
        holed = substitute_node(root, 4, Goal(4, parse("Raa")))
        partial = realise(holed)

        self.assertFalse(partial.complete)
        self.assertEqual(partial.open_goals, (4,))
        self.assertGreater(len(partial.proofs), 0)
        self.assertLess(len(partial.proofs), len(whole.proofs))
        self.assertTrue(
            all(f.kind == "blocked" for f in partial.failures.values()),
            partial.failures,
        )

    def test_a_branch_beside_a_hole_is_still_verified(self):
        left = self.builder.assume(self.p)
        step = Step(50, "∧Intro", (left, Goal(51, self.q)))
        realisation = realise(step)
        self.assertIn(left.id, realisation.proofs)
        self.assertEqual(realisation.proofs[left.id].conclusion, self.p)


class TestFailureIsLocal(RealiseTestCase):
    def test_one_bad_step_leaves_its_siblings_checked(self):
        """Otherwise every keystroke would blank the whole drawing."""
        good = self.builder.step("∧Intro", [self.builder.assume(self.p),
                                            self.builder.assume(self.q)])
        bad = self.builder.step("∧Elim1", [self.builder.assume(self.p)])
        root = self.builder.step("∧Intro", [good, bad])
        realisation = realise(root)

        self.assertIn(good.id, realisation.proofs)
        self.assertEqual(realisation.failures[bad.id].kind, "shape")
        self.assertEqual(realisation.failures[root.id].kind, "blocked")
        self.assertIsNone(realisation.proof)

    def test_a_failure_names_the_node_it_happened_at(self):
        bad = self.builder.step("∧Elim1", [self.builder.assume(self.p)])
        failure = realise(bad).failures[bad.id]
        self.assertEqual(failure.node, bad.id)
        self.assertEqual(failure.rule, "∧Elim1")
        self.assertIn("conjunction", failure.message)


class TestDrift(RealiseTestCase):
    def test_a_step_that_no_longer_proves_its_claim_says_so(self):
        """Editing above a step can change what it concludes; say where."""
        step = Step(
            60,
            "∧Intro",
            (self.builder.assume(self.p), self.builder.assume(self.q)),
            (),
            claim=parse("P & S"),
        )
        realisation = realise(step)
        failure = realisation.failures[60]
        self.assertEqual(failure.kind, "drift")
        self.assertIn("P ∧ S", failure.message)
        self.assertIn("P ∧ Q", failure.message)

    def test_the_proof_survives_a_drift_because_it_proves_something(self):
        step = Step(
            61,
            "∧Intro",
            (self.builder.assume(self.p), self.builder.assume(self.q)),
            (),
            claim=parse("P & S"),
        )
        realisation = realise(step)
        self.assertEqual(realisation.proof.conclusion, parse("P & Q"))


class TestContexts(RealiseTestCase):
    def test_premises_are_available_everywhere(self):
        goal = Goal(70, self.p)
        document = Document(goal=self.p, premises=(self.q,), cards=(Card(goal),))
        self.assertEqual(contexts(document)[70], frozenset({self.q}))

    def test_a_discharging_step_adds_to_the_branch_below_it(self):
        goal = Goal(71, self.q)
        step = Step(72, "→Intro", (goal,), (Binding("assumption", self.p),))
        document = Document(goal=parse("P -> Q"), cards=(Card(step),))
        found = contexts(document)
        self.assertEqual(found[72], frozenset())
        self.assertEqual(found[71], frozenset({self.p}))

    def test_context_is_computed_from_the_current_tree_not_remembered(self):
        """Editing the discharge changes what the goal below may assume."""
        goal = Goal(73, self.q)
        step = Step(74, "→Intro", (goal,), (Binding("assumption", self.p),))
        document = Document(cards=(Card(step),))
        self.assertEqual(contexts(document)[73], frozenset({self.p}))

        moved = Step(74, "→Intro", (goal,), (Binding("assumption", parse("S")),))
        self.assertEqual(
            contexts(Document(cards=(Card(moved),)))[73], frozenset({parse("S")})
        )

    def test_classical_negation_offers_its_own_denial_in_both_branches(self):
        """The whole trick of reductio, made visible before it is used."""
        left, right = Goal(75, self.q), Goal(76, Not(self.q))
        step = Step(77, "¬Elim", (left, right), (Binding("conclusion", self.p),))
        found = contexts(Document(cards=(Card(step),)))
        self.assertEqual(found[75], frozenset({Not(self.p)}))
        self.assertEqual(found[76], frozenset({Not(self.p)}))
