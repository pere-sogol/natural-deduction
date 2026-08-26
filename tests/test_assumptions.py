"""Tests for ndweb.assumptions: what a block rests on.

The load-bearing one is :class:`TestItAgreesWithTheEngine`.  This module
works out open assumptions from the tree alone, so that a block with holes
in it can still say what it rests on -- which duplicates bookkeeping
``Proof.assumptions`` already does exactly.  A duplicate is only safe
while something checks it, so for every block the editor can realise the
two are required to agree, the same trick ``tests/test_discharge.py``
plays for the discharge sets and ``parse(str(f)) == f`` plays for the
printer.
"""

import unittest

from nd.formula import Not, reset_arities
from nd.parser import parse
from nd.proofs import rule_catalogue
from nd.rules import Assumption

from ndweb.assumptions import SELF_RESTING, Rest, leaves, rests, tally
from ndweb.derivation import Binding, Card, Document, Goal, Step
from ndweb.exercises import EXERCISES, Builder, solution
from ndweb.realise import realise
from ndweb.session import Session


class AssumptionsTestCase(unittest.TestCase):
    def setUp(self):
        reset_arities()
        self.p, self.q, self.r = parse("P"), parse("Q"), parse("R")
        self.builder = Builder()

    def texts(self, found):
        return [str(entry.formula) for entry in found]


class TestWhatCountsAsALeaf(AssumptionsTestCase):
    def test_an_assumption_block_rests_on_itself(self):
        found = leaves(self.builder.assume(self.p))
        self.assertEqual(self.texts(found), ["P"])
        self.assertFalse(found[0].slot)
        self.assertFalse(found[0].discharged)

    def test_a_slot_written_into_rests_on_itself_too(self):
        """Nothing in the calculus tells the two apart: both are leaves."""
        found = leaves(Goal(1, self.p))
        self.assertEqual(self.texts(found), ["P"])
        self.assertTrue(found[0].slot)

    def test_a_blank_slot_rests_on_nothing_because_nothing_is_written(self):
        self.assertEqual(leaves(Goal(1)), ())

    def test_equality_intro_rests_on_nothing_at_all(self):
        """a = a is a theorem, so it is the leaf that is not an assumption."""
        step = Step(2, "=Intro", (), (Binding("constant", parse("a=a").left),))
        self.assertEqual(leaves(step), ())

    def test_a_sentence_the_editor_merely_worked_out_is_not_assumed(self):
        """A suggestion in a slot is nobody's assumption until it is typed.

        ->Elim reads its left premise off the conditional on the right, and
        shows it -- but the student has not written it, and the engine will
        not treat it as written either.
        """
        step = Step(3, "→Elim", (Goal(4), self.builder.assume(parse("P -> Q"))))
        self.assertEqual(self.texts(leaves(step)), ["P → Q"])

    def test_the_self_resting_rules_are_the_ones_the_engine_says_they_are(self):
        """A new leaf rule must not quietly fall out of the table."""
        for cls in rule_catalogue():
            if cls.subproof_count:
                continue
            self.assertEqual(cls.name in SELF_RESTING, cls is Assumption, cls.name)
        self.assertEqual(SELF_RESTING, frozenset({Assumption.name}))


class TestDischarge(AssumptionsTestCase):
    def test_a_step_below_closes_the_leaf_it_discharges(self):
        step = Step(5, "→Intro", (self.builder.assume(self.p),),
                    (Binding("assumption", self.p),))
        found = leaves(step)
        self.assertEqual(self.texts(found), ["P"])
        self.assertTrue(found[0].discharged)

    def test_one_discharge_closes_every_leaf_labelled_with_it(self):
        """As(pi) is a set of sentences, not of nodes."""
        both = Step(6, "∧Intro", (self.builder.assume(self.p),
                                  self.builder.assume(self.p)))
        step = Step(7, "→Intro", (both,), (Binding("assumption", self.p),))
        found = leaves(step)
        self.assertEqual(len(found), 2)
        self.assertTrue(all(leaf.discharged for leaf in found))

    def test_a_leaf_in_a_branch_the_step_does_not_reach_stays_open(self):
        """vElim closes the left disjunct in pi_1 only."""
        left = self.builder.assume(self.p)
        right = self.builder.assume(self.p)
        step = Step(8, "∨Elim", (left, right,
                                 self.builder.assume(parse("P | Q"))))
        found = dict((leaf.node, leaf.discharged) for leaf in leaves(step))
        self.assertTrue(found[left.id])
        self.assertFalse(found[right.id])


class TestRests(AssumptionsTestCase):
    def test_the_same_sentence_in_two_places_is_one_assumption(self):
        step = Step(9, "∧Intro", (Goal(10, self.p), Goal(11, self.p)))
        found = rests(step)
        self.assertEqual(self.texts(found), ["P"])
        self.assertEqual(found[0].nodes, (10, 11))
        self.assertEqual(found[0].slots, (10, 11))

    def test_a_premise_is_marked_as_one(self):
        step = Step(12, "∧Intro", (Goal(13, self.p), Goal(14, self.q)))
        found = dict((str(entry.formula), entry) for entry
                     in rests(step, frozenset({self.p})))
        self.assertTrue(found["P"].premise)
        self.assertFalse(found["Q"].premise)

    def test_a_discharged_sentence_is_kept_but_no_longer_open(self):
        step = Step(15, "→Intro", (Goal(16, self.p),),
                    (Binding("assumption", self.p),))
        found = rests(step)
        self.assertEqual(self.texts(found), ["P"])
        self.assertFalse(found[0].open)
        self.assertEqual(found[0].closed, (16,))

    def test_it_is_sorted_so_a_panel_does_not_reshuffle(self):
        step = Step(17, "∧Intro", (Goal(18, self.r), Goal(19, self.p)))
        self.assertEqual(self.texts(rests(step)), ["P", "R"])


class TestItAgreesWithTheEngine(AssumptionsTestCase):
    """The copy must not drift from what ``Proof.assumptions`` records."""

    def test_every_recorded_solution_rests_on_what_its_proof_does(self):
        for exercise in EXERCISES:
            reset_arities()
            root = solution(exercise.key)
            realisation = realise(root)
            self.assertTrue(realisation.complete, exercise.key)
            self.assertEqual(
                frozenset(entry.formula for entry in rests(root) if entry.open),
                realisation.proof.assumptions,
                exercise.key,
            )

    def test_it_agrees_when_the_leaves_are_slots_rather_than_blocks(self):
        """Which is the case the engine could not have been asked about."""
        step = Step(20, "→Intro",
                    (Step(21, "∧Intro", (Goal(22, self.p), Goal(23, self.q))),),
                    (Binding("assumption", self.p),))
        realisation = realise(step)
        self.assertEqual(
            frozenset(entry.formula for entry in rests(step) if entry.open),
            realisation.proof.assumptions,
        )

    def test_it_agrees_through_the_classical_negation_rules(self):
        step = Step(24, "¬Elim", (Goal(25, self.q), Goal(26, Not(self.q))),
                    (Binding("conclusion", self.p),))
        realisation = realise(step)
        self.assertEqual(
            frozenset(entry.formula for entry in rests(step) if entry.open),
            realisation.proof.assumptions,
        )


class TestTally(AssumptionsTestCase):
    def make(self, goal, premises, *nodes):
        return Document(
            goal=parse(goal),
            premises=tuple(parse(text) for text in premises),
            cards=tuple(Card(node) for node in nodes),
        )

    def test_a_premise_nothing_has_used_is_still_listed(self):
        found = tally(self.make("Q", ["P", "R"], Goal(30, self.p)))
        self.assertEqual(self.texts(found.premises), ["P", "R"])
        self.assertEqual(found.premises[0].nodes, (30,))
        self.assertEqual(found.premises[1].nodes, ())

    def test_an_assumption_that_was_not_given_is_the_work_that_is_left(self):
        found = tally(self.make("Q", ["P"], Goal(31, self.r)))
        self.assertEqual(self.texts(found.extra), ["R"])
        self.assertFalse(found.settled)

    def test_a_blank_slot_is_counted_separately_from_an_assumption(self):
        step = Step(32, "∧Intro", (Goal(33, self.p), Goal(34)))
        found = tally(self.make("P & Q", ["P"], step))
        self.assertEqual(found.blanks, (34,))
        self.assertEqual(found.extra, ())
        self.assertFalse(found.settled)

    def test_a_sheet_resting_only_on_its_premises_is_settled(self):
        step = Step(35, "∧Intro", (Goal(36, self.p), Goal(37, self.q)))
        found = tally(self.make("P & Q", ["P", "Q"], step))
        self.assertEqual(found.extra, ())
        self.assertEqual(found.blanks, ())
        self.assertTrue(found.settled)

    def test_the_same_sentence_across_two_blocks_is_one_row(self):
        found = tally(self.make("Q", ["P"], Goal(38, self.p), Goal(39, self.p)))
        self.assertEqual(len(found.premises), 1)
        self.assertEqual(found.premises[0].nodes, (38, 39))

    def test_a_repeated_premise_is_listed_once(self):
        document = Document(premises=(self.p, self.p))
        self.assertEqual(self.texts(tally(document).premises), ["P"])


class TestThroughTheSession(AssumptionsTestCase):
    """What the browser is actually handed."""

    def state(self, goal, premises):
        session = Session()
        return session, session.dispatch(
            {"op": "new", "goal": goal, "premises": premises})

    def test_the_goal_written_down_is_reported_as_merely_assumed(self):
        _, state = self.state("Q", ["P"])
        self.assertIn("only assumed", state["assumptions"]["verdict"])
        self.assertFalse(state["solved"])

    def test_writing_the_premises_into_the_slots_proves_the_sequent(self):
        """The whole point: no ceremony, just sentences at the top."""
        session, state = self.state("Q", ["P -> Q", "P"])
        goal = state["cards"][-1]["root"]
        state = session.dispatch({"op": "place", "rule": "→Elim", "slot": goal})
        children = [n["id"] for n in state["cards"][-1]["tree"]["premises"]]
        state = session.dispatch(
            {"op": "set", "node": children[0], "text": "P"})
        state = session.dispatch(
            {"op": "set", "node": children[1], "text": "P -> Q"})

        self.assertTrue(state["solved"])
        self.assertTrue(state["assumptions"]["settled"])
        self.assertEqual(state["assumptions"]["extra"], [])
        self.assertIn("proved", state["assumptions"]["verdict"])

    def test_an_assumption_that_is_not_a_premise_is_named(self):
        session, state = self.state("Q", ["P -> Q"])
        goal = state["cards"][-1]["root"]
        state = session.dispatch({"op": "place", "rule": "→Elim", "slot": goal})
        children = [n["id"] for n in state["cards"][-1]["tree"]["premises"]]
        state = session.dispatch(
            {"op": "set", "node": children[0], "text": "P"})
        state = session.dispatch(
            {"op": "set", "node": children[1], "text": "P -> Q"})

        self.assertFalse(state["solved"])
        self.assertEqual(
            [row["text"] for row in state["assumptions"]["extra"]], ["P"])
        self.assertIn("rests on P", state["assumptions"]["verdict"])

    def test_a_blank_slot_is_reported_as_blank_rather_than_assumed(self):
        session, state = self.state("P & Q", ["P", "Q"])
        goal = state["cards"][-1]["root"]
        state = session.dispatch({"op": "place", "rule": "∧Intro", "slot": goal})
        self.assertEqual(len(state["blankSlots"]), 2)
        self.assertEqual(state["assumptions"]["extra"], [])
        self.assertIn("blank", state["assumptions"]["verdict"])

    def test_every_card_carries_its_own_assumptions(self):
        _, state = self.state("Q", ["P"])
        for drawn in state["cards"]:
            for row in drawn["assumptions"]:
                self.assertIn("pieces", row)
                self.assertTrue(row["text"])

    def test_the_tracker_is_json(self):
        import json

        _, state = self.state("Q", ["P -> Q", "P"])
        json.dumps(state["assumptions"], ensure_ascii=False)


class TestRestDefaults(unittest.TestCase):
    def test_a_rest_with_no_open_leaves_is_not_open(self):
        reset_arities()
        self.assertFalse(Rest(parse("P")).open)
