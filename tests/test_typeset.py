"""Tests for ndweb.typeset: a proof as a nesting, and a sentence as pieces.

Two contracts.  The pieces of a sentence put back together are the printed
sentence exactly, so whatever the browser sets is what the parser reads --
the same discipline ``parse(str(f)) == f`` imposes on the printer.  And the
nesting carries every node of the derivation once, with the book's own
discharge numbers on it, because those come from ``nd.render.layout``
rather than from a second implementation of the numbering.
"""

import json
import unittest

from nd.formula import reset_arities
from nd.parser import parse
from nd.proofs import rule_catalogue
from nd.render import layout

from ndweb.catalogue import SCHEMA
from ndweb.derivation import Binding, Card, Goal, Step
from ndweb.exercises import EXERCISES, solution
from ndweb.realise import realise
from ndweb.shadow import shadow
from ndweb.typeset import card, pieces, schema, typeset
from ndweb.unify import solve

CORPUS = [
    "P",
    "¬P",
    "P ∧ Q",
    "P ∨ ¬Q",
    "P → (Q ↔ S)",
    "∀x Fx",
    "∀x(Fx → ∃y Rxy)",
    "∀x∃y Rxy",
    "∀x¬Fx",
    "a=b",
    "∀x x=x",
    "Loves(a, b)",
    "Loves(a_1, b_12) ∧ ¬A(x_3)",
    "Raa → ∃x Rxa",
]


class TestPieces(unittest.TestCase):
    def setUp(self):
        reset_arities()

    def test_the_pieces_put_back_together_are_the_sentence(self):
        """Nothing is dropped: a tightened space is marked, not removed."""
        for text in CORPUS:
            joined = "".join(piece["t"] for piece in pieces(text))
            self.assertEqual(joined, text)

    def test_what_is_set_is_what_the_parser_reads_back(self):
        for text in CORPUS:
            reset_arities()
            formula = parse(text)
            joined = "".join(piece["t"] for piece in pieces(str(formula)))
            self.assertEqual(parse(joined), formula)

    def test_a_predicate_letter_is_told_from_its_terms(self):
        """Rxy is one letter and two terms; the parser decides it that way."""
        self.assertEqual(
            [(p["c"], p["t"]) for p in pieces("Rxy")],
            [("pred", "R"), ("var", "x"), ("var", "y")],
        )

    def test_a_bracketed_name_keeps_all_its_letters(self):
        self.assertEqual(pieces("Loves(a, b)")[0], {"c": "pred", "t": "Loves"})

    def test_variables_and_constants_are_told_apart(self):
        classes = dict((p["t"], p["c"]) for p in pieces("Rxa"))
        self.assertEqual(classes["x"], "var")
        self.assertEqual(classes["a"], "const")

    def test_a_subscript_keeps_its_underscore_as_a_piece_of_its_own(self):
        self.assertEqual(
            [(p["c"], p["t"]) for p in pieces("a_12")],
            [("const", "a"), ("under", "_"), ("sub", "12")],
        )

    def test_the_space_a_connective_supplies_itself_is_marked_not_dropped(self):
        classes = [p["c"] for p in pieces("P ∧ Q")]
        self.assertEqual(classes.count("tight"), 2)
        self.assertNotIn("gap", classes)

    def test_a_space_that_is_not_a_connective_s_is_left_alone(self):
        self.assertIn("gap", [p["c"] for p in pieces("∀x Fx")])


class TestSchemas(unittest.TestCase):
    def setUp(self):
        reset_arities()

    def test_every_rule_has_a_figure(self):
        for cls in rule_catalogue():
            self.assertIn(cls.name, SCHEMA, cls.name)

    def test_a_figure_has_as_many_premises_as_the_rule_takes(self):
        for cls in rule_catalogue():
            self.assertEqual(
                len(SCHEMA[cls.name][0]), cls.subproof_count, cls.name)

    def test_a_figure_carries_the_rule_s_own_label(self):
        self.assertEqual(schema("∨Elim")["label"], "∨E")

    def test_the_disjunction_comes_last_as_the_constructor_takes_it(self):
        """∨Elim(π₁, π₂, π₃) surprises people; the figure should teach it."""
        self.assertEqual(SCHEMA["∨Elim"][0][2], "φ ∨ ψ")

    def test_a_figure_says_what_it_discharges(self):
        drawn = schema("→Intro")
        self.assertTrue(drawn["premises"][0]["brackets"])
        self.assertEqual(drawn["premises"][0]["discharged"], "φ")


class TestTheNesting(unittest.TestCase):
    def setUp(self):
        reset_arities()

    def flatten(self, node):
        found = []
        for child in node["premises"]:
            found.extend(self.flatten(child))
        found.append(node)
        return found

    def test_every_node_of_the_derivation_appears_exactly_once(self):
        for exercise in EXERCISES:
            reset_arities()
            root = solution(exercise.key)
            drawn = self.flatten(typeset(root))
            ids = [node["id"] for node in drawn]
            self.assertEqual(len(ids), len(set(ids)), exercise.key)
            self.assertEqual(len(ids), len(list(_walk(root))), exercise.key)

    def test_the_discharge_numbers_are_the_renderer_s_own(self):
        """They are read off layout rather than worked out a second time."""
        for exercise in EXERCISES:
            reset_arities()
            root = solution(exercise.key)
            found = solve(root)
            realisation = realise(root, found)
            placed = layout(shadow(root, realisation, found), ascii_only=True)
            drawn = self.flatten(typeset(root, realisation, found))
            self.assertEqual(
                [node["conclusion"]["discharged"] for node in drawn],
                [spot.discharge for spot in placed.formulae],
                exercise.key,
            )

    def test_a_leaf_rule_is_set_without_a_bar(self):
        """=Intro and Assumption have nothing above them, and no bar either."""
        drawn = typeset(Step(0, "Assumption", (), (), parse("P")))
        self.assertEqual(drawn["premises"], [])
        self.assertEqual(drawn["label"], "")

    def test_a_blank_slot_says_it_is_blank(self):
        drawn = typeset(Goal(0))
        self.assertEqual(drawn["kind"], "slot")
        self.assertEqual(drawn["conclusion"]["source"], "blank")
        self.assertEqual(drawn["conclusion"]["pieces"], [])

    def test_a_slot_holding_something_else_is_not_bracketed(self):
        """The step closes P; the slot says Q, so nothing is discharged."""
        step = Step(0, "→Intro", (Goal(1, parse("Q")),), (), parse("P -> Q"))
        drawn = typeset(step)
        self.assertIsNone(drawn["premises"][0]["conclusion"]["discharged"])

    def test_a_slot_holding_what_the_step_closes_is_bracketed(self):
        """Writing at the top of a step assumes it, so it can be closed."""
        step = Step(0, "→Intro", (Goal(1, parse("P")),), (), parse("P -> P"))
        drawn = typeset(step)
        self.assertEqual(drawn["premises"][0]["conclusion"]["discharged"], 1)
        self.assertEqual(drawn["number"], 1)

    def test_a_blank_slot_is_never_bracketed(self):
        """It rests on nothing yet; the bracket would say something false."""
        step = Step(0, "→Intro", (Goal(1),), (Binding("assumption", parse("P")),))
        drawn = typeset(step)
        self.assertIsNone(drawn["premises"][0]["conclusion"]["discharged"])

    def test_a_slot_the_engine_refuses_says_why_rather_than_staying_quiet(self):
        """Fx is not a sentence, and no work above the slot will fix that."""
        drawn = typeset(Step(0, "∨Intro", (Goal(1, parse("Fx")),), (),
                             parse("P | P")))
        slot = drawn["premises"][0]
        self.assertEqual(slot["status"], "sentence")
        self.assertIn("sentence", slot["message"])

    def test_a_step_waiting_on_a_branch_is_pending_rather_than_wrong(self):
        step = Step(0, "∧Intro", (Goal(1), Goal(2)))
        drawn = typeset(step)
        self.assertEqual(drawn["status"], "pending")
        self.assertEqual(drawn["message"], "")

    def test_an_empty_parameter_is_pending_but_still_says_what_is_missing(self):
        """Unlike a branch above, nothing that happens elsewhere will fill it."""
        step = Step(0, "∧Elim", (Step(1, "Assumption", (), (), parse("P & Q")),))
        drawn = typeset(step)
        self.assertEqual(drawn["status"], "pending")
        self.assertEqual(drawn["message"], "the conclusion is still empty")

    def test_a_card_carries_where_it_sits_and_what_it_proves(self):
        reset_arities()
        drawn = card(Card(solution("identity"), 30, 70))
        self.assertEqual((drawn["x"], drawn["y"]), (30, 70))
        self.assertTrue(drawn["complete"])
        self.assertEqual(drawn["conclusion"], "P → P")
        self.assertEqual(drawn["open"], [])

    def test_the_whole_thing_is_json(self):
        for exercise in EXERCISES:
            reset_arities()
            json.dumps(card(Card(solution(exercise.key))), ensure_ascii=False)


def _walk(node):
    if isinstance(node, Step):
        for child in node.children:
            for found in _walk(child):
                yield found
    yield node
