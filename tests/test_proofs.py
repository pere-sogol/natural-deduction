"""Tests for the proof tree itself: nd.proofs."""

import unittest

from nd.formula import Constant, Variable, reset_arities
from nd.parser import parse
from nd.proofs import (
    MismatchError,
    Proof,
    ProofError,
    SentenceError,
    ShapeError,
    apply,
    can_apply,
    rule,
    rule_catalogue,
)
from nd.rules import (
    AndElim,
    AndIntro,
    Assumption,
    EqualityIntro,
    ForallIntro,
    ImpliesElim,
    ImpliesIntro,
    NotIntro,
    OrElim,
)


class ProofTestCase(unittest.TestCase):
    """Arities are module-level state, so start each case from a clean one."""

    def setUp(self):
        reset_arities()
        self.p = parse("P")
        self.q = parse("Q")
        self.s = parse("S")


class TestAssumptions(ProofTestCase):
    """As(pi): a set of sentences, not of nodes."""

    def test_an_assumption_rests_on_itself(self):
        proof = Assumption(self.p)
        self.assertEqual(proof.conclusion, self.p)
        self.assertEqual(proof.assumptions, frozenset({self.p}))

    def test_equality_intro_rests_on_nothing(self):
        proof = EqualityIntro(Constant("a"))
        self.assertEqual(proof.conclusion, parse("a=a"))
        self.assertEqual(proof.assumptions, frozenset())

    def test_assumptions_accumulate(self):
        proof = AndIntro(Assumption(self.p), Assumption(self.q))
        self.assertEqual(proof.assumptions, frozenset({self.p, self.q}))

    def test_one_discharge_closes_every_matching_leaf(self):
        # The same sentence at two leaves is one assumption, and one
        # discharge closes both -- As(pi) is a set of sentences.
        both = AndIntro(Assumption(self.p), Assumption(self.p))
        self.assertEqual(both.assumptions, frozenset({self.p}))
        self.assertEqual(len(list(both.leaves())), 2)
        discharged = ImpliesIntro(both, self.p)
        self.assertEqual(discharged.assumptions, frozenset())

    def test_discharge_reaches_only_its_own_subproof(self):
        left = ImpliesIntro(Assumption(self.p), self.p)
        proof = AndIntro(left, Assumption(self.p))
        self.assertEqual(proof.assumptions, frozenset({self.p}))

    def test_vacuous_discharge_is_allowed(self):
        # Nothing in the subproof is discharged, and P -> Q follows anyway.
        proof = ImpliesIntro(Assumption(self.q), self.p)
        self.assertEqual(proof.conclusion, parse("P -> Q"))
        self.assertEqual(proof.assumptions, frozenset({self.q}))

    def test_discharged_runs_parallel_to_subproofs(self):
        proof = ImpliesIntro(Assumption(self.p), self.p)
        self.assertEqual(len(proof.discharged), len(proof.subproofs))
        self.assertEqual(proof.discharged, (frozenset({self.p}),))

    def test_or_elim_discharges_each_case_separately(self):
        proof = OrElim(
            Assumption(self.s),
            Assumption(self.s),
            Assumption(parse("P | Q")),
        )
        self.assertEqual(proof.conclusion, self.s)
        self.assertEqual(proof.assumptions, frozenset({self.s, parse("P | Q")}))
        self.assertEqual(
            proof.discharged,
            (frozenset({self.p}), frozenset({self.q}), frozenset()),
        )


class TestStructure(ProofTestCase):
    def test_nodes_and_leaves(self):
        proof = AndIntro(Assumption(self.p), Assumption(self.q))
        self.assertEqual(len(list(proof.nodes())), 3)
        self.assertEqual(
            [leaf.conclusion for leaf in proof.leaves()], [self.p, self.q]
        )
        self.assertTrue(Assumption(self.p).is_leaf)
        self.assertFalse(proof.is_leaf)

    def test_length_is_the_longest_branch(self):
        self.assertEqual(Assumption(self.p).length(), 1)
        conjunction = AndIntro(Assumption(self.p), Assumption(self.q))
        self.assertEqual(conjunction.length(), 2)
        self.assertEqual(AndElim(conjunction, self.p).length(), 3)

    def test_size_counts_every_node(self):
        conjunction = AndIntro(Assumption(self.p), Assumption(self.q))
        self.assertEqual(conjunction.size(), 3)
        self.assertEqual(AndElim(conjunction, self.p).size(), 4)

    def test_constants_and_predicates_span_the_whole_tree(self):
        proof = ImpliesElim(
            Assumption(parse("Fa")), Assumption(parse("Fa -> Gb"))
        )
        self.assertEqual(
            proof.constants(), frozenset({Constant("a"), Constant("b")})
        )
        self.assertEqual(proof.predicates(), frozenset({("F", 1), ("G", 1)}))

    def test_proves_and_is_theorem(self):
        theorem = ImpliesIntro(Assumption(self.p), self.p)
        self.assertTrue(theorem.is_theorem())
        self.assertTrue(theorem.proves(parse("P -> P")))
        self.assertFalse(theorem.proves(parse("P -> Q")))

        conditional = Assumption(self.p)
        self.assertFalse(conditional.is_theorem())
        self.assertTrue(conditional.proves(self.p, {self.p, self.q}))
        self.assertFalse(conditional.proves(self.p, {self.q}))


class TestInvariants(ProofTestCase):
    def test_every_line_must_be_a_sentence(self):
        with self.assertRaises(SentenceError) as caught:
            Assumption(parse("Fx"))
        self.assertIn("sentence", str(caught.exception))
        self.assertIn("x", str(caught.exception))

    def test_a_proof_is_immutable(self):
        proof = Assumption(self.p)
        with self.assertRaises(AttributeError):
            proof.conclusion = self.q
        with self.assertRaises(AttributeError):
            del proof.conclusion

    def test_proofs_are_equal_structurally(self):
        first = AndIntro(Assumption(self.p), Assumption(self.q))
        second = AndIntro(Assumption(self.p), Assumption(self.q))
        self.assertEqual(first, second)
        self.assertEqual(hash(first), hash(second))
        self.assertEqual(len({first, second}), 1)

    def test_different_rules_reaching_one_conclusion_differ(self):
        # P v P follows from P either way, but the proofs are not the same.
        from nd.rules import OrIntro1, OrIntro2

        leaf = Assumption(self.p)
        self.assertNotEqual(OrIntro1(leaf, self.p), OrIntro2(leaf, self.p))

    def test_one_rule_reaching_two_conclusions_differs_from_itself(self):
        # ^Elim is one rule taking either conjunct, so the conjunct taken
        # is what tells the two proofs apart.
        conjunction = AndIntro(Assumption(self.p), Assumption(self.q))
        self.assertNotEqual(
            AndElim(conjunction, self.p), AndElim(conjunction, self.q)
        )

    def test_the_discharged_sentence_is_part_of_a_proof_s_identity(self):
        subproof = Assumption(self.p)
        self.assertNotEqual(
            ImpliesIntro(subproof, self.q), ImpliesIntro(subproof, self.s)
        )

    def test_a_formula_where_a_subproof_belongs_is_refused(self):
        with self.assertRaises(TypeError) as caught:
            AndIntro(self.p, Assumption(self.q))
        self.assertIn("Assumption(P)", str(caught.exception))


class TestRegistry(ProofTestCase):
    """What a user interface builds its palette from."""

    def test_every_rule_is_registered_under_both_spellings(self):
        self.assertEqual(len(rule_catalogue()), 20)
        for cls in rule_catalogue():
            self.assertIs(rule(cls.name), cls)
            self.assertIs(rule(cls.__name__), cls)

    def test_unknown_rule_names_list_the_known_ones(self):
        with self.assertRaises(KeyError) as caught:
            rule("∧Elim3")
        self.assertIn("∧Elim, ∧Intro", str(caught.exception))

    def test_apply_builds_by_name(self):
        proof = apply("∧Intro", [Assumption(self.p), Assumption(self.q)])
        self.assertEqual(proof.conclusion, parse("P & Q"))
        self.assertEqual(
            proof, apply("AndIntro", [Assumption(self.p), Assumption(self.q)])
        )

    def test_apply_passes_parameters_by_keyword(self):
        proof = apply("→Intro", [Assumption(self.p)], assumption=self.q)
        self.assertEqual(proof.conclusion, parse("Q -> P"))

    def test_can_apply_reports_what_apply_would_raise(self):
        self.assertIsNone(
            can_apply("∧Intro", [Assumption(self.p), Assumption(self.q)])
        )
        error = can_apply("∧Elim", [Assumption(self.p)], conclusion=self.p)
        self.assertIsInstance(error, ShapeError)
        self.assertEqual(error.rule_name, "∧Elim")
        self.assertIn("conjunction", error.message)

    def test_can_apply_catches_provisos_too(self):
        error = can_apply(
            "∀Intro",
            [Assumption(parse("Fa"))],
            constant=Constant("a"),
            variable=Variable("x"),
        )
        self.assertIsInstance(error, ProofError)
        self.assertIn("arbitrary", str(error))

    def test_parameters_describe_what_a_rule_still_needs(self):
        self.assertEqual(rule("∧Intro").parameters, ())
        names = [p.name for p in rule("∃Intro").parameters]
        self.assertEqual(names, ["conclusion", "constant"])
        self.assertFalse(rule("∃Intro").parameters[1].required)

    def test_subproof_counts_are_declared(self):
        self.assertEqual(rule("Assumption").subproof_count, 0)
        self.assertEqual(rule("∧Elim").subproof_count, 1)
        self.assertEqual(rule("∧Intro").subproof_count, 2)
        self.assertEqual(rule("∨Elim").subproof_count, 3)

    def test_declared_counts_match_the_trees_built(self):
        # A rule that took a different number of subproofs than it
        # advertises would break a palette built from the catalogue.
        built = {
            "Assumption": Assumption(self.p),
            "∧Intro": AndIntro(Assumption(self.p), Assumption(self.q)),
            "→Intro": ImpliesIntro(Assumption(self.p), self.q),
            "∨Elim": OrElim(
                Assumption(self.s), Assumption(self.s), Assumption(parse("P | Q"))
            ),
        }
        for name, proof in built.items():
            self.assertEqual(len(proof.subproofs), rule(name).subproof_count, name)


class TestRepr(ProofTestCase):
    def test_repr_names_the_rule_and_the_conclusion(self):
        self.assertEqual(repr(Assumption(self.p)), "<Assumption |- P>")
        self.assertEqual(
            repr(AndIntro(Assumption(self.p), Assumption(self.q))),
            "<∧Intro |- P ∧ Q>",
        )

    def test_str_draws_the_tree(self):
        # The detail belongs to tests.test_render; this is the hand-off.
        self.assertIn("→I", str(ImpliesIntro(Assumption(self.p), self.p)))


if __name__ == "__main__":
    unittest.main()
