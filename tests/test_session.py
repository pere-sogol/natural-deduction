"""Tests for ndweb.session, which is the whole editor as a library.

These drive the literal path the browser drives: a dict in, a dict out,
with ``json.dumps`` over the result.  That last check is not incidental --
it is what stops a ``Formula`` leaking across the boundary, which is the
easiest mistake to make here and the hardest to see.
"""

import json
import unittest

from nd.formula import reset_arities

from ndweb.session import Session


def nodes(state):
    """Every node of every block on the sheet, innermost first."""
    found = []

    def descend(node):
        for child in node["premises"]:
            descend(child)
        found.append(node)

    for card in state["cards"]:
        descend(card["tree"])
    return found


def saying(state, text, kind=None):
    """The id of the first node whose line reads ``text``."""
    for node in nodes(state):
        if node["conclusion"]["text"] == text:
            if kind is None or node["kind"] == kind:
                return node["id"]
    raise AssertionError(
        "nothing on the sheet reads {0!r}; there is {1}".format(
            text, [n["conclusion"]["text"] for n in nodes(state)]
        )
    )


def node(state, node_id):
    for found in nodes(state):
        if found["id"] == node_id:
            return found
    raise AssertionError("no node {0}".format(node_id))


class SessionTestCase(unittest.TestCase):
    def setUp(self):
        reset_arities()
        self.session = Session()

    def go(self, **action):
        return self.session.dispatch(action)

    def start(self, key="identity"):
        return self.go(op="exercise", key=key)

    def blank(self, goal="", premises=()):
        return self.go(op="new", goal=goal, premises=list(premises))


class TestTheBoundary(SessionTestCase):
    def test_every_state_is_json(self):
        """A Formula that leaked into the view would stop the app dead."""
        state = self.start("russell")
        json.dumps(state, ensure_ascii=False)
        state = self.go(op="place", rule="¬Elim", slot=saying(state, "P"))
        json.dumps(state, ensure_ascii=False)

    def test_an_unknown_action_is_reported_not_raised(self):
        state = self.go(op="wibble")
        self.assertIn("unknown action", state["notice"])

    def test_an_unknown_rule_is_reported_not_raised(self):
        state = self.go(op="place", rule="∧Wibble")
        self.assertIn("no rule called", state["notice"])

    def test_a_bad_formula_comes_back_as_a_notice(self):
        state = self.go(op="new", goal="P ->")
        self.assertIn("column", state["notice"])


class TestStarting(SessionTestCase):
    def test_an_exercise_lays_out_its_premises_and_its_goal(self):
        state = self.start("distribute")
        self.assertEqual(state["sequent"], "∀x(Fx → Gx), ∀x Fx ⊢ ∀x Gx")
        self.assertEqual(len(state["cards"]), 3)  # two premises and the goal
        self.assertEqual(len(state["openSlots"]), 1)

    def test_a_sheet_may_have_no_goal_at_all(self):
        """An empty sheet is a legitimate place to work."""
        state = self.blank()
        self.assertEqual(state["cards"], [])
        self.assertEqual(state["sequent"], "")

    def test_the_library_comes_with_the_state(self):
        self.assertEqual(len(self.start()["exercises"]), 10)

    def test_clearing_keeps_the_sequent(self):
        state = self.start("distribute")
        state = self.go(op="clear")
        self.assertEqual(state["cards"], [])
        self.assertEqual(state["sequent"], "∀x(Fx → Gx), ∀x Fx ⊢ ∀x Gx")


class TestPuttingRulesDown(SessionTestCase):
    def test_a_rule_lands_on_the_sheet_with_every_slot_empty(self):
        """No dialogue, nothing settled: the block is filled in afterwards."""
        state = self.blank()
        state = self.go(op="place", rule="∧Intro", x=120, y=80)
        card = state["cards"][0]
        self.assertEqual((card["x"], card["y"]), (120, 80))
        self.assertEqual(card["tree"]["conclusion"]["source"], "blank")
        self.assertEqual(
            [p["conclusion"]["source"] for p in card["tree"]["premises"]],
            ["blank", "blank"],
        )

    def test_a_rule_dropped_on_a_slot_inherits_what_it_said(self):
        state = self.start()
        state = self.go(op="place", rule="→Intro", slot=saying(state, "P → P"))
        self.assertEqual(node(state, 0)["conclusion"]["text"], "P → P")
        self.assertEqual(saying(state, "P", "slot") is not None, True)

    def test_a_rule_that_cannot_conclude_the_goal_is_still_allowed(self):
        """The sandbox lets it be put down; the bar then says it is wrong."""
        state = self.start()
        state = self.go(op="place", rule="∧Intro", slot=saying(state, "P → P"))
        self.assertEqual(state["notice"], "")
        self.assertIn("conjunction", node(state, 0)["note"])

    def test_every_rule_stays_in_the_palette_whatever_is_selected(self):
        state = self.start()
        self.go(op="focus", node=saying(state, "P → P"))
        state = self.go(op="view")
        self.assertEqual(len(state["palette"]), 17)
        misfits = [r["name"] for r in state["palette"] if not r["fits"]]
        self.assertIn("∧Intro", misfits)
        self.assertNotIn("→Intro", misfits)


class TestWritingInSlots(SessionTestCase):
    def test_writing_the_premises_works_out_the_conclusion(self):
        state = self.blank()
        state = self.go(op="place", rule="∧Intro")
        left, right = [p["id"] for p in state["cards"][0]["tree"]["premises"]]
        self.go(op="set", node=left, text="P")
        state = self.go(op="set", node=right, text="Q")
        self.assertEqual(state["cards"][0]["tree"]["conclusion"]["text"], "P ∧ Q")

    def test_writing_the_conclusion_works_out_the_premises(self):
        state = self.blank()
        state = self.go(op="place", rule="∧Intro")
        root = state["cards"][0]["root"]
        state = self.go(op="set", node=root, text="P & Q")
        self.assertEqual(
            [p["conclusion"]["text"] for p in state["cards"][0]["tree"]["premises"]],
            ["P", "Q"],
        )

    def test_one_premise_and_the_conclusion_settle_the_other_premise(self):
        """→Elim's antecedent used to be asked for in a dialogue."""
        state = self.blank()
        state = self.go(op="place", rule="→Elim")
        left = state["cards"][0]["tree"]["premises"][0]["id"]
        self.go(op="set", node=state["cards"][0]["root"], text="Q")
        state = self.go(op="set", node=left, text="P")
        self.assertEqual(
            state["cards"][0]["tree"]["premises"][1]["conclusion"]["text"], "P → Q"
        )

    def test_the_conditional_alone_settles_the_whole_of_an_arrow_elimination(self):
        state = self.blank()
        state = self.go(op="place", rule="→Elim")
        right = state["cards"][0]["tree"]["premises"][1]["id"]
        state = self.go(op="set", node=right, text="P -> Q")
        tree = state["cards"][0]["tree"]
        self.assertEqual(tree["conclusion"]["text"], "Q")
        self.assertEqual(tree["premises"][0]["conclusion"]["text"], "P")

    def test_what_was_written_is_told_apart_from_what_was_worked_out(self):
        state = self.blank()
        state = self.go(op="place", rule="∧Intro")
        root = state["cards"][0]["root"]
        state = self.go(op="set", node=root, text="P & Q")
        tree = state["cards"][0]["tree"]
        self.assertEqual(tree["conclusion"]["source"], "written")
        self.assertEqual(tree["premises"][0]["conclusion"]["source"], "derived")

    def test_a_slot_can_be_emptied_again(self):
        state = self.blank()
        state = self.go(op="place", rule="∧Intro")
        root = state["cards"][0]["root"]
        self.go(op="set", node=root, text="P & Q")
        state = self.go(op="set", node=root, text="")
        self.assertEqual(state["cards"][0]["tree"]["conclusion"]["source"], "blank")

    def test_a_sentence_that_will_not_parse_leaves_the_sheet_alone(self):
        state = self.blank()
        state = self.go(op="place", rule="∧Intro")
        root = state["cards"][0]["root"]
        state = self.go(op="set", node=root, text="P &")
        self.assertIn("column", state["notice"])
        self.assertEqual(state["cards"][0]["tree"]["conclusion"]["source"], "blank")


class TestParameters(SessionTestCase):
    def test_a_parameter_is_a_slot_like_any_other(self):
        state = self.blank()
        state = self.go(op="place", rule="∀Elim")
        root = state["cards"][0]["root"]
        premise = state["cards"][0]["tree"]["premises"][0]["id"]
        self.go(op="set", node=premise, text="Ax Fx")
        state = self.go(op="param", node=root, name="constant", text="b")
        self.assertEqual(state["cards"][0]["tree"]["conclusion"]["text"], "Fb")

    def test_the_parameter_that_is_the_conclusion_is_not_asked_for_twice(self):
        state = self.blank()
        state = self.go(op="place", rule="Assumption")
        state = self.go(op="set", node=state["cards"][0]["root"], text="P")
        self.assertEqual(state["cards"][0]["tree"]["params"], [])
        self.assertTrue(state["cards"][0]["complete"])

    def test_a_constant_slot_refuses_a_variable(self):
        state = self.blank()
        state = self.go(op="place", rule="∀Elim")
        state = self.go(op="param", node=state["cards"][0]["root"],
                        name="constant", text="x")
        self.assertIn("must be a constant", state["notice"])

    def test_a_parameter_can_be_cleared(self):
        state = self.blank()
        state = self.go(op="place", rule="∀Elim")
        root = state["cards"][0]["root"]
        self.go(op="param", node=root, name="constant", text="b")
        state = self.go(op="param", node=root, name="constant", text="")
        params = dict((p["name"], p["source"]) for p in
                      state["cards"][0]["tree"]["params"])
        self.assertEqual(params["constant"], "blank")


class TestJoiningAndParting(SessionTestCase):
    def two_blocks(self):
        """A ∧Intro claiming P ∧ Q, its right half filled, and a loose P."""
        state = self.blank()
        state = self.go(op="place", rule="∧Intro", x=40, y=40)
        state = self.go(op="set", node=state["cards"][0]["root"], text="P & Q")
        right = state["cards"][0]["tree"]["premises"][1]["id"]
        state = self.go(op="place", rule="Assumption", slot=right)
        state = self.go(op="place", rule="Assumption", x=300, y=40)
        loose = state["cards"][-1]["root"]
        state = self.go(op="set", node=loose, text="P")
        return state, loose

    def test_a_block_drops_into_a_slot(self):
        state, loose = self.two_blocks()
        slot = state["cards"][0]["tree"]["premises"][0]["id"]
        state = self.go(op="attach", slot=slot, source=loose)
        self.assertEqual(len(state["cards"]), 1)
        self.assertEqual(
            state["cards"][0]["tree"]["premises"][0]["conclusion"]["text"], "P"
        )

    def test_a_block_proving_something_else_still_drops_in(self):
        """Refusing would leave the student holding it with no explanation.

        The checker says what is wrong on the bar, which is more use.
        """
        state, loose = self.two_blocks()
        self.go(op="set", node=loose, text="S")
        state = self.go(op="view")
        slot = state["cards"][0]["tree"]["premises"][0]["id"]
        state = self.go(op="attach", slot=slot, source=loose)
        self.assertEqual(state["notice"], "")
        self.assertEqual(node(state, 0)["status"], "drift")
        self.assertIn("now proves S ∧ Q", node(state, 0)["message"])

    def test_a_block_cannot_be_dropped_into_itself(self):
        state = self.blank()
        state = self.go(op="place", rule="∧Intro")
        root = state["cards"][0]["root"]
        slot = state["cards"][0]["tree"]["premises"][0]["id"]
        state = self.go(op="attach", slot=slot, source=root)
        self.assertIn("into itself", state["notice"])

    def test_a_branch_pulls_off_and_leaves_a_slot_saying_what_it_said(self):
        state, loose = self.two_blocks()
        slot = state["cards"][0]["tree"]["premises"][0]["id"]
        state = self.go(op="attach", slot=slot, source=loose)
        state = self.go(op="detach", node=loose, x=500, y=500)
        self.assertEqual(len(state["cards"]), 2)
        self.assertEqual(
            state["cards"][0]["tree"]["premises"][0]["conclusion"]["text"], "P"
        )
        self.assertEqual([c for c in state["cards"] if c["root"] == loose][0]["x"], 500)

    def test_deleting_a_branch_leaves_an_empty_slot(self):
        state, loose = self.two_blocks()
        slot = state["cards"][0]["tree"]["premises"][0]["id"]
        state = self.go(op="attach", slot=slot, source=loose)
        state = self.go(op="delete", node=loose)
        self.assertEqual(len(state["cards"]), 1)
        self.assertEqual(
            state["cards"][0]["tree"]["premises"][0]["conclusion"]["text"], "P"
        )

    def test_deleting_a_whole_card_takes_it_off_the_sheet(self):
        state, loose = self.two_blocks()
        state = self.go(op="delete", node=loose)
        self.assertEqual(len(state["cards"]), 1)

    def test_a_card_can_be_moved(self):
        state = self.blank()
        state = self.go(op="place", rule="∧Intro", x=10, y=10)
        root = state["cards"][0]["root"]
        state = self.go(op="move", root=root, x=333, y=222)
        self.assertEqual((state["cards"][0]["x"], state["cards"][0]["y"]), (333, 222))


class TestProving(SessionTestCase):
    def test_a_finished_block_proving_the_sequent_is_recognised(self):
        state = self.start()
        state = self.go(op="place", rule="→Intro", slot=saying(state, "P → P"))
        state = self.go(op="place", rule="Assumption", slot=saying(state, "P", "slot"))
        self.assertTrue(state["solved"])
        self.assertEqual(state["openSlots"], [])
        self.assertEqual(state["provedBy"], 0)

    def test_a_proof_of_the_goal_counts_wherever_it_sits(self):
        """There is no privileged tree; a block is the answer by proving it.

        The goal's own card is left untouched here, and the sequent is still
        proved -- by a block built somewhere else entirely on the sheet.
        """
        state = self.blank(goal="P -> P")
        state = self.go(op="place", rule="→Intro", x=400, y=400)
        built = state["cards"][-1]
        state = self.go(op="set", node=built["root"], text="P -> P")
        state = self.go(op="place", rule="Assumption",
                        slot=state["cards"][-1]["tree"]["premises"][0]["id"])
        self.assertTrue(state["solved"])
        self.assertEqual(state["provedBy"], built["root"])
        self.assertNotEqual(state["provedBy"], state["cards"][0]["root"])

    def test_a_fresh_parameter_is_chosen_rather_than_asked_for(self):
        state = self.blank(goal="Ax Gx", premises=["Fa"])
        state = self.go(op="place", rule="∀Intro", slot=saying(state, "∀x Gx"))
        params = dict((p["name"], p["text"]) for p in node(state, 1)["params"])
        self.assertNotEqual(params["constant"], "a")  # a is taken by the premise
        self.assertEqual(params["variable"], "x")
        self.assertEqual(node(state, 1)["note"], "")

    def test_a_proviso_that_cannot_be_settled_yet_is_a_warning_not_an_error(self):
        """Whether c stays arbitrary depends on branches not yet built."""
        state = self.blank(goal="Ax Gx", premises=["Fa"])
        state = self.go(op="place", rule="∀Intro", slot=saying(state, "∀x Gx"))
        state = self.go(op="param", node=1, name="constant", text="a")
        self.assertIn("arbitrary", node(state, 1)["note"])
        self.assertEqual(node(state, 1)["status"], "pending")

    def test_generalising_on_a_constant_in_the_goal_is_refused_outright(self):
        """Raa generalises to Ax Rxx, never to Ax Rxa: that branch is dead."""
        state = self.blank(goal="Ax Rxa")
        root = state["cards"][0]["root"]
        state = self.go(op="place", rule="∀Intro", slot=root)
        state = self.go(op="param", node=root, name="constant", text="a")
        self.assertIn("already occurs", node(state, root)["note"])


class TestHistory(SessionTestCase):
    def test_undo_puts_the_slot_back(self):
        state = self.start()
        state = self.go(op="place", rule="→Intro", slot=saying(state, "P → P"))
        self.assertTrue(state["canUndo"])
        state = self.go(op="undo")
        self.assertEqual(node(state, 0)["kind"], "slot")
        self.assertTrue(state["canRedo"])

    def test_redo_puts_it_back_again(self):
        state = self.start()
        self.go(op="place", rule="→Intro", slot=saying(state, "P → P"))
        self.go(op="undo")
        state = self.go(op="redo")
        self.assertFalse(state["canRedo"])
        self.assertEqual(node(state, 0)["kind"], "step")

    def test_a_new_move_after_undoing_drops_the_future(self):
        state = self.start()
        self.go(op="place", rule="→Intro", slot=saying(state, "P → P"))
        self.go(op="undo")
        state = self.go(op="place", rule="¬Elim", slot=saying(state, "P → P"))
        self.assertFalse(state["canRedo"])

    def test_undoing_at_the_start_is_harmless(self):
        state = self.go(op="undo")
        self.assertFalse(state["canUndo"])


class TestSharing(SessionTestCase):
    def test_the_state_carries_a_link_to_itself(self):
        state = self.start("russell")
        other = Session()
        restored = other.dispatch(
            {"op": "load-fragment", "fragment": state["fragment"]}
        )
        self.assertEqual(restored["sequent"], state["sequent"])

    def test_a_half_built_sheet_shares_too(self):
        state = self.blank()
        state = self.go(op="place", rule="∨Elim", x=90, y=90)
        other = Session()
        restored = other.dispatch(
            {"op": "load-fragment", "fragment": state["fragment"]}
        )
        self.assertEqual((restored["cards"][0]["x"], restored["cards"][0]["y"]),
                         (90, 90))
