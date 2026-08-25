"""Tests for the editor's own tree: ndweb.derivation."""

import unittest

from nd.formula import reset_arities
from nd.parser import parse

from ndweb.derivation import (
    Binding,
    Card,
    Document,
    Goal,
    Step,
    detach_node,
    expected,
    find,
    kwargs,
    parameters,
    substitute_node,
    walk,
)


class DerivationTestCase(unittest.TestCase):
    def setUp(self):
        reset_arities()
        self.p, self.q = parse("P"), parse("Q")

    def tree(self):
        """AndIntro over two assumptions: ids 1, 2, 3."""
        return Step(
            3,
            "∧Intro",
            (
                Step(1, "Assumption", (), (), self.p),
                Step(2, "Assumption", (), (), self.q),
            ),
        )


class TestStructure(DerivationTestCase):
    def test_walk_yields_children_before_parents(self):
        self.assertEqual([node.id for node in walk(self.tree())], [1, 2, 3])

    def test_find_reaches_inside_every_card_on_the_sheet(self):
        document = Document(
            cards=(Card(Goal(9, self.p)), Card(self.tree())), next_id=10
        )
        self.assertEqual(find(document, 9).id, 9)
        self.assertEqual(find(document, 2).id, 2)
        self.assertIsNone(find(document, 99))

    def test_detaching_leaves_a_slot_saying_what_was_there(self):
        """Pulling a branch off must not also lose what belonged in its place."""
        tree = self.tree()
        left, taken = detach_node(tree, 1)
        self.assertEqual(taken.id, 1)
        self.assertIsInstance(left.children[0], Goal)
        self.assertEqual(left.children[0].target, self.p)
        self.assertIs(left.children[1], tree.children[1])

    def test_detaching_can_be_told_what_to_leave(self):
        """A block built upwards claims nothing, so it must be told."""
        tree = Step(3, "∧Intro", (Step(1, "Assumption", (), (), self.p), Goal(2)))
        left, taken = detach_node(tree, 1, parse("Q"))
        self.assertEqual(left.children[0].target, parse("Q"))

    def test_a_root_cannot_be_detached_from_itself(self):
        tree = self.tree()
        left, taken = detach_node(tree, tree.id)
        self.assertIs(left, tree)
        self.assertIsNone(taken)

    def test_substitution_shares_every_untouched_branch(self):
        """Structural sharing is what lets a cache survive an edit elsewhere."""
        tree = self.tree()
        changed = substitute_node(tree, 1, Goal(1, self.p))
        self.assertIsNot(changed, tree)
        self.assertIsInstance(changed.children[0], Goal)
        self.assertIs(changed.children[1], tree.children[1])

    def test_substituting_nothing_returns_the_very_same_object(self):
        tree = self.tree()
        self.assertIs(substitute_node(tree, 404, Goal(404, self.p)), tree)


class TestClaims(DerivationTestCase):
    def test_a_slot_expects_its_target(self):
        self.assertEqual(expected(Goal(1, self.p)), self.p)

    def test_a_slot_may_be_blank(self):
        """A rule can be put down long before there is a plan for it."""
        self.assertIsNone(expected(Goal(1)))
        self.assertTrue(Goal(1).is_blank)

    def test_a_forward_step_claims_nothing(self):
        """It follows its premises wherever they go; there is no target."""
        self.assertIsNone(expected(self.tree()))

    def test_a_backward_step_remembers_what_it_was_built_to_prove(self):
        pinned = Step(4, "∧Intro", (), (), claim=parse("P & Q"))
        self.assertEqual(expected(pinned), parse("P & Q"))


class TestBindings(DerivationTestCase):
    def test_bindings_become_the_keywords_apply_wants(self):
        """Parameter.name is the constructor keyword, so this splats."""
        step = Step(1, "→Intro", (), (Binding("assumption", self.p),))
        self.assertEqual(kwargs(step), {"assumption": self.p})

    def test_the_conclusion_fills_the_parameter_that_is_the_conclusion(self):
        """Assumption takes the sentence it assumes, and that is the line.

        Typing it twice would let the two disagree, so the line fills it.
        """
        step = Step(1, "Assumption", (), (), claim=self.p)
        self.assertEqual(kwargs(step), {"formula": self.p})

    def test_a_written_binding_still_wins(self):
        step = Step(1, "Assumption", (), (Binding("formula", self.q),), claim=self.p)
        self.assertEqual(kwargs(step), {"formula": self.q})

    def test_that_parameter_is_not_offered_as_a_slot_of_its_own(self):
        self.assertEqual([p.name for p in parameters("Assumption")], [])
        self.assertEqual([p.name for p in parameters("→Intro")], ["assumption"])


class TestDocument(DerivationTestCase):
    def test_ids_are_spent_not_reused(self):
        document = Document(next_id=7)
        first, document = document.fresh()
        second, document = document.fresh()
        self.assertEqual((first, second, document.next_id), (7, 8, 9))

    def test_ids_can_be_spent_in_a_batch(self):
        ids, document = Document(next_id=4).spend(3)
        self.assertEqual((ids, document.next_id), ([4, 5, 6], 7))

    def test_roots_are_the_cards_on_the_sheet(self):
        document = Document(cards=(Card(Goal(1, self.p)), Card(self.tree())))
        self.assertEqual([root.id for root in document.roots], [1, 3])
        self.assertEqual(Document().roots, ())

    def test_a_card_remembers_where_it_was_put(self):
        """Position is the student's arrangement, and nothing else reads it."""
        card = Card(Goal(1, self.p), 220, 140)
        self.assertEqual((card.x, card.y), (220, 140))
