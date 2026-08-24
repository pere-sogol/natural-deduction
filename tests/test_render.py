"""Tests for drawing a proof: nd.render."""

import textwrap
import unittest

from nd.formula import Constant, Variable, reset_arities
from nd.parser import parse
from nd.render import layout, to_text
from nd.rules import (
    AndIntro,
    Assumption,
    EqualityIntro,
    ExistsElim,
    ForallElim,
    ForallIntro,
    ImpliesElim,
    ImpliesIntro,
    NotElim,
    NotIntro,
    OrIntro1,
    OrIntro2,
)


class RenderTestCase(unittest.TestCase):
    def setUp(self):
        reset_arities()
        self.a = Constant("a")
        self.x = Variable("x")

    def assertDrawn(self, proof, expected, ascii_only=False):
        self.assertEqual(
            to_text(proof, ascii_only), textwrap.dedent(expected).strip("\n")
        )


class TestDrawing(RenderTestCase):
    def test_a_bare_assumption_is_just_its_sentence(self):
        self.assertDrawn(Assumption(parse("P")), "P")

    def test_discharge_is_bracketed_and_numbered(self):
        self.assertDrawn(
            ImpliesIntro(Assumption(parse("P")), parse("P")),
            """
             [P]¹
            ───── →I, 1
            P → P
            """,
        )

    def test_an_undischarged_assumption_is_left_bare(self):
        self.assertDrawn(
            ImpliesElim(Assumption(parse("P")), Assumption(parse("P -> Q"))),
            """
            P   P → Q
            ───────── →E
                Q
            """,
        )

    def test_a_vacuous_discharge_earns_no_number(self):
        # Nothing below is closed by this step, so a number would point
        # at nothing.
        self.assertDrawn(
            ImpliesIntro(Assumption(parse("Q")), parse("P")),
            """
              Q
            ───── →I
            P → Q
            """,
        )

    def test_one_discharge_marks_every_matching_leaf(self):
        both = AndIntro(Assumption(parse("P")), Assumption(parse("P")))
        self.assertDrawn(
            ImpliesIntro(both, parse("P")),
            """
            [P]¹   [P]¹
            ─────────── ∧I
               P ∧ P
             ───────── →I, 1
             P → P ∧ P
            """,
        )

    def test_numbers_grow_down_the_page(self):
        inner = ImpliesElim(
            Assumption(parse("P")), Assumption(parse("P -> Q"))
        )
        proof = ImpliesIntro(ImpliesIntro(inner, parse("P")), parse("P -> Q"))
        self.assertDrawn(
            proof,
            """
            [P]¹   [P → Q]²
            ─────────────── →E
                   Q
                 ───── →I, 1
                 P → Q
            ─────────────── →I, 2
            (P → Q) → P → Q
            """,
        )

    def test_the_innermost_step_owns_the_leaf(self):
        # Both steps discharge P; the inner one is what closes the leaf,
        # so the marker is 1 and the outer step gets no number.
        inner = ImpliesIntro(Assumption(parse("P")), parse("P"))
        drawn = to_text(ImpliesIntro(inner, parse("P")))
        self.assertIn("[P]¹", drawn)
        self.assertIn("→I, 1", drawn)
        self.assertNotIn("→I, 2", drawn)

    def test_equality_intro_is_labelled_where_it_stands(self):
        # A leaf that is not an assumption; without the note it would be
        # indistinguishable from one.
        self.assertDrawn(
            ForallIntro(EqualityIntro(self.a), self.a, self.x),
            """
              a=a  =I
            ────── ∀I
            ∀x x=x
            """,
        )

    def test_a_predicate_proof(self):
        denial = Assumption(parse("Ax ~Fx"))
        contradiction = NotIntro(
            Assumption(parse("Fa")), ForallElim(denial, self.a), parse("Ax ~Fx")
        )
        self.assertDrawn(
            ExistsElim(Assumption(parse("Ex Fx")), contradiction, self.a),
            """
                            [∀x¬Fx]¹
                            ──────── ∀E
                    [Fa]²     ¬Fa
                    ───────────── ¬I, 1
            ∃x Fx      ¬∀x¬Fx
            ───────────────── ∃E, 2
                 ¬∀x¬Fx
            """,
        )

    def test_a_leaf_that_is_not_an_assumption_is_never_bracketed(self):
        # =Intro rests on nothing, so a step discharging a=a has not
        # closed it and must not mark it as though it had.
        proof = ImpliesIntro(EqualityIntro(self.a), parse("a=a"))
        self.assertEqual(proof.assumptions, frozenset())
        self.assertDrawn(
            proof,
            """
               a=a  =I
            ───────── →I
            a=a → a=a
            """,
        )

    def test_ascii_only_changes_the_bars_and_the_numbers(self):
        self.assertDrawn(
            ImpliesIntro(Assumption(parse("P")), parse("P")),
            """
             [P]1
            ----- →I, 1
            P → P
            """,
            ascii_only=True,
        )

    def test_no_line_carries_trailing_space(self):
        proof = NotElim(
            OrIntro2(
                NotIntro(
                    OrIntro1(Assumption(parse("P")), parse("~P")),
                    Assumption(parse("~(P | ~P)")),
                    parse("P"),
                ),
                parse("P"),
            ),
            Assumption(parse("~(P | ~P)")),
            parse("P | ~P"),
        )
        for line in to_text(proof).split("\n"):
            self.assertEqual(line, line.rstrip())


class TestLayout(RenderTestCase):
    """The placement stage, which a graphical front end would reuse."""

    def _proof(self):
        return ImpliesIntro(
            ImpliesElim(Assumption(parse("P")), Assumption(parse("P -> Q"))),
            parse("P"),
        )

    def test_dimensions_match_the_drawing(self):
        proof = self._proof()
        placed = layout(proof)
        lines = to_text(proof).split("\n")
        self.assertEqual(placed.height, len(lines))
        self.assertEqual(placed.width, max(len(line) for line in lines))

    def test_every_node_is_placed_once(self):
        proof = self._proof()
        placed = layout(proof)
        self.assertEqual(len(placed.formulae), proof.size())
        self.assertEqual(
            len(placed.bars), sum(1 for node in proof.nodes() if not node.is_leaf)
        )

    def test_a_discharged_leaf_carries_its_number(self):
        placed = layout(self._proof())
        marked = [f for f in placed.formulae if f.discharge is not None]
        self.assertEqual(len(marked), 1)
        self.assertEqual(marked[0].formula, parse("P"))
        self.assertEqual(marked[0].discharge, 1)
        self.assertEqual(marked[0].text, "[P]¹")

    def test_conclusions_are_centred_under_their_bars(self):
        denial = Assumption(parse("Ax ~Fx"))
        contradiction = NotIntro(
            Assumption(parse("Fa")), ForallElim(denial, self.a), parse("Ax ~Fx")
        )
        proof = ExistsElim(Assumption(parse("Ex Fx")), contradiction, self.a)
        placed = layout(proof)
        by_position = {(f.x, f.y): f for f in placed.formulae}
        for bar in placed.bars:
            below = [
                f
                for (x, y), f in by_position.items()
                if y == bar.y + 1 and bar.x <= x and x + len(f.text) <= bar.x + bar.width
            ]
            self.assertEqual(len(below), 1, "one conclusion under each bar")
            conclusion = below[0]
            left = conclusion.x - bar.x
            right = (bar.x + bar.width) - (conclusion.x + len(conclusion.text))
            self.assertLessEqual(abs(left - right), 1)

    def test_a_wide_conclusion_widens_its_bar(self):
        # The premise is narrow and the conclusion is not; the bar has to
        # cover the wider of the two, and nothing may fall off the left.
        proof = ImpliesIntro(Assumption(parse("P")), parse("Ax(Fx -> Gx)"))
        placed = layout(proof)
        self.assertTrue(all(f.x >= 0 for f in placed.formulae))
        self.assertTrue(all(b.x >= 0 for b in placed.bars))
        bar = placed.bars[0]
        self.assertEqual(bar.width, len(str(proof.conclusion)))


if __name__ == "__main__":
    unittest.main()
