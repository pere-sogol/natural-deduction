"""Tests for ndweb.discharge.

The point of this module is the agreement test.  ``discharges`` works out
what a step closes without building it, which duplicates knowledge held
in ``nd.rules``; the duplication is only safe because every step the
editor can actually realise is checked against the engine's own
``Proof.discharged`` here.
"""

import unittest

from nd.formula import Not, reset_arities
from nd.parser import parse

from ndweb.derivation import Binding, Step, walk
from ndweb.discharge import discharges
from ndweb.exercises import EXERCISES, Builder, solution
from ndweb.realise import realise, resolver


class TestAgreesWithTheEngine(unittest.TestCase):
    def test_every_realisable_step_matches_what_the_proof_records(self):
        for exercise in EXERCISES:
            reset_arities()
            root = solution(exercise.key)
            realisation = realise(root)
            self.assertTrue(realisation.complete, exercise.key)
            resolve = resolver(realisation)
            checked = 0
            for node in walk(root):
                if not isinstance(node, Step) or node.is_leaf:
                    continue
                proof = realisation.proofs[node.id]
                self.assertEqual(
                    discharges(node, resolve),
                    proof.discharged,
                    "{0}: {1} at node {2}".format(exercise.key, node.rule, node.id),
                )
                checked += 1
            self.assertGreater(checked, 0, exercise.key)


class TestByRule(unittest.TestCase):
    def setUp(self):
        reset_arities()
        self.p, self.q = parse("P"), parse("Q")
        self.builder = Builder()

    def test_a_rule_that_discharges_nothing_reports_empty_sets(self):
        step = self.builder.step("∧Intro", [self.builder.assume(self.p),
                                            self.builder.assume(self.q)])
        self.assertEqual(discharges(step), (frozenset(), frozenset()))

    def test_conditional_introduction_closes_its_antecedent(self):
        step = self.builder.step("→Intro", [self.builder.assume(self.q)],
                                 assumption=self.p)
        self.assertEqual(discharges(step), (frozenset({self.p}),))

    def test_classical_negation_closes_the_negation_of_its_conclusion(self):
        step = Step(1, "¬Elim", (self.builder.goal(self.q),
                                 self.builder.goal(Not(self.q))),
                    (Binding("conclusion", self.p),))
        self.assertEqual(discharges(step),
                         (frozenset({Not(self.p)}), frozenset({Not(self.p)})))

    def test_biconditional_introduction_crosses_its_branches(self):
        """pi_1 proves the right half from the left, and pi_2 the reverse."""
        step = Step(1, "↔Intro", (self.builder.goal(self.q),
                                  self.builder.goal(self.p)), ())
        self.assertEqual(discharges(step),
                         (frozenset({self.p}), frozenset({self.q})))

    def test_disjunction_elimination_splits_the_disjuncts(self):
        step = Step(1, "∨Elim", (self.builder.goal(parse("S")),
                                 self.builder.goal(parse("S")),
                                 self.builder.goal(parse("P | Q"))), ())
        self.assertEqual(
            discharges(step),
            (frozenset({self.p}), frozenset({self.q}), frozenset()),
        )

    def test_unknown_children_give_empty_sets_rather_than_wrong_ones(self):
        """A skeleton with nothing known yet must not invent a discharge."""
        step = Step(1, "∨Elim", (Step(2, "∧Intro"), Step(3, "∧Intro"),
                                 Step(4, "∧Intro")), ())
        self.assertEqual(discharges(step),
                         (frozenset(), frozenset(), frozenset()))


class TestParallelToChildren(unittest.TestCase):
    """The result must line up with the children, as Proof.discharged does.

    ``Proof._seal`` refuses a discharge list of the wrong length, so a
    step still being assembled -- with too few children, or none yet --
    must report nothing rather than a set it cannot place.
    """

    def setUp(self):
        reset_arities()

    def test_every_rule_at_every_arity(self):
        from nd.proofs import rule_catalogue

        p = parse("P")
        for cls in rule_catalogue():
            for count in range(4):
                children = tuple(
                    Step(index + 100, "Assumption", (), (Binding("formula", p),))
                    for index in range(count)
                )
                params = tuple(
                    Binding(parameter.name, p)
                    for parameter in cls.parameters
                    if parameter.kind == "formula"
                )
                step = Step(1, cls.name, children, params)
                self.assertEqual(
                    len(discharges(step)),
                    count,
                    "{0} with {1} children".format(cls.name, count),
                )
