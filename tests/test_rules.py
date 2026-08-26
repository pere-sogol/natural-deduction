"""Tests for the inference rules: nd.rules.

Each rule gets a case that applies it and a case per way of getting it
wrong, since the refusals are as much a part of the system as the
successes -- they are what a student will actually see.
"""

import unittest

from nd.formula import Constant, Variable, reset_arities
from nd.parser import parse
from nd.proofs import MismatchError, ProvisoError, ShapeError
from nd.rules import (
    AndElim,
    AndIntro,
    Assumption,
    EqualityElim,
    EqualityIntro,
    ExistsElim,
    ExistsIntro,
    ForallElim,
    ForallIntro,
    IffElim,
    IffIntro,
    ImpliesElim,
    ImpliesIntro,
    NotElim,
    NotIntro,
    OrElim,
    OrIntro,
    _replaces_some,
)


class RuleTestCase(unittest.TestCase):
    def setUp(self):
        reset_arities()
        self.x, self.y = Variable("x"), Variable("y")
        self.a, self.b, self.c = Constant("a"), Constant("b"), Constant("c")

    def assertRefuses(self, error, fragment, function, *args, **kwargs):
        with self.assertRaises(error) as caught:
            function(*args, **kwargs)
        self.assertIn(fragment, str(caught.exception))
        return caught.exception


class TestConjunction(RuleTestCase):
    def test_intro(self):
        proof = AndIntro(Assumption(parse("P")), Assumption(parse("Q")))
        self.assertEqual(proof.conclusion, parse("P & Q"))

    def test_elim_takes_either_conjunct(self):
        """One rule, not two: the conjunct wanted is named, not chosen up front."""
        conjunction = Assumption(parse("P & Q"))
        self.assertEqual(AndElim(conjunction, parse("P")).conclusion, parse("P"))
        self.assertEqual(AndElim(conjunction, parse("Q")).conclusion, parse("Q"))

    def test_elim_refuses_a_conclusion_that_is_neither_conjunct(self):
        self.assertRefuses(
            MismatchError, "neither conjunct",
            AndElim, Assumption(parse("P & Q")), parse("S"),
        )

    def test_elim_takes_a_conjunct_whole_rather_than_reaching_inside_it(self):
        """From (P ^ Q) ^ S only P ^ Q and S are reachable, not P."""
        conjunction = Assumption(parse("(P & Q) & S"))
        self.assertEqual(
            AndElim(conjunction, parse("P & Q")).conclusion, parse("P & Q")
        )
        self.assertRefuses(
            MismatchError, "neither conjunct",
            AndElim, conjunction, parse("P"),
        )

    def test_elim_needs_a_conjunction(self):
        self.assertRefuses(
            ShapeError, "must conclude with a conjunction",
            AndElim, Assumption(parse("P | Q")), parse("P"),
        )


class TestDisjunction(RuleTestCase):
    def test_intro_adds_a_disjunct_on_either_side(self):
        """One rule, not two: the whole disjunction says which side."""
        proof = Assumption(parse("P"))
        self.assertEqual(
            OrIntro(proof, parse("P | Q")).conclusion, parse("P | Q")
        )
        self.assertEqual(
            OrIntro(proof, parse("Q | P")).conclusion, parse("Q | P")
        )

    def test_intro_refuses_a_disjunction_the_premise_is_no_part_of(self):
        self.assertRefuses(
            MismatchError, "neither disjunct",
            OrIntro, Assumption(parse("P")), parse("Q | S"),
        )

    def test_intro_needs_a_disjunction_to_claim(self):
        self.assertRefuses(
            ShapeError, "must be a disjunction",
            OrIntro, Assumption(parse("P")), parse("P & Q"),
        )

    def test_elim(self):
        proof = OrElim(
            Assumption(parse("S")),
            Assumption(parse("S")),
            Assumption(parse("P | Q")),
        )
        self.assertEqual(proof.conclusion, parse("S"))

    def test_elim_discharges_a_disjunct_from_each_case(self):
        # P v Q, P -> S, Q -> S |- S
        left = ImpliesElim(Assumption(parse("P")), Assumption(parse("P -> S")))
        right = ImpliesElim(Assumption(parse("Q")), Assumption(parse("Q -> S")))
        proof = OrElim(left, right, Assumption(parse("P | Q")))
        self.assertEqual(proof.conclusion, parse("S"))
        self.assertEqual(
            proof.assumptions,
            frozenset({parse("P | Q"), parse("P -> S"), parse("Q -> S")}),
        )

    def test_the_cases_must_agree(self):
        self.assertRefuses(
            MismatchError, "same conclusion",
            OrElim,
            Assumption(parse("S")),
            Assumption(parse("T")),
            Assumption(parse("P | Q")),
        )

    def test_elim_needs_a_disjunction(self):
        self.assertRefuses(
            ShapeError, "must conclude with a disjunction",
            OrElim,
            Assumption(parse("S")),
            Assumption(parse("S")),
            Assumption(parse("P & Q")),
        )


class TestConditional(RuleTestCase):
    def test_intro_discharges_the_antecedent(self):
        proof = ImpliesIntro(Assumption(parse("P")), parse("P"))
        self.assertEqual(proof.conclusion, parse("P -> P"))
        self.assertTrue(proof.is_theorem())

    def test_elim(self):
        proof = ImpliesElim(
            Assumption(parse("P")), Assumption(parse("P -> Q"))
        )
        self.assertEqual(proof.conclusion, parse("Q"))

    def test_elim_needs_the_antecedent_to_match(self):
        self.assertRefuses(
            MismatchError, "the antecedent of",
            ImpliesElim, Assumption(parse("S")), Assumption(parse("P -> Q")),
        )

    def test_elim_needs_a_conditional(self):
        self.assertRefuses(
            ShapeError, "must conclude with a conditional",
            ImpliesElim, Assumption(parse("P")), Assumption(parse("P & Q")),
        )


class TestNegation(RuleTestCase):
    """No absurdity sign: the rules act on a contradictory pair directly."""

    def test_intro(self):
        # P -> Q, P -> ~Q |- ~P
        assumed = Assumption(parse("P"))
        positive = ImpliesElim(assumed, Assumption(parse("P -> Q")))
        negative = ImpliesElim(assumed, Assumption(parse("P -> ~Q")))
        proof = NotIntro(positive, negative, parse("P"))
        self.assertEqual(proof.conclusion, parse("~P"))
        self.assertEqual(
            proof.assumptions,
            frozenset({parse("P -> Q"), parse("P -> ~Q")}),
        )

    def test_elim_discharges_the_negation_of_its_conclusion(self):
        # ~~P |- P
        negated = Assumption(parse("~P"))
        proof = NotElim(negated, Assumption(parse("~~P")), parse("P"))
        self.assertEqual(proof.conclusion, parse("P"))
        self.assertEqual(proof.assumptions, frozenset({parse("~~P")}))

    def test_double_negation_elimination_is_a_theorem(self):
        negated = Assumption(parse("~P"))
        inner = NotElim(negated, Assumption(parse("~~P")), parse("P"))
        proof = ImpliesIntro(inner, parse("~~P"))
        self.assertEqual(proof.conclusion, parse("~~P -> P"))
        self.assertTrue(proof.is_theorem())

    def test_excluded_middle_is_a_theorem(self):
        excluded = parse("P | ~P")
        denial = Assumption(parse("~(P | ~P)"))
        left = OrIntro(Assumption(parse("P")), excluded)
        not_p = NotIntro(left, denial, parse("P"))
        right = OrIntro(not_p, excluded)
        proof = NotElim(right, denial, excluded)
        self.assertEqual(proof.conclusion, excluded)
        self.assertTrue(proof.is_theorem())

    def test_the_pair_must_be_contradictory(self):
        self.assertRefuses(
            MismatchError, "contradictory pair",
            NotIntro, Assumption(parse("P")), Assumption(parse("Q")), parse("S"),
        )
        self.assertRefuses(
            MismatchError, "contradictory pair",
            NotElim, Assumption(parse("P")), Assumption(parse("~Q")), parse("S"),
        )


class TestBiconditional(RuleTestCase):
    def test_intro_takes_the_right_half_first(self):
        # pi_1 proves phi_2 from phi_1, pi_2 proves phi_1 from phi_2.
        proof = IffIntro(Assumption(parse("Q")), Assumption(parse("P")))
        self.assertEqual(proof.conclusion, parse("P <-> Q"))
        self.assertEqual(
            proof.discharged,
            (frozenset({parse("P")}), frozenset({parse("Q")})),
        )

    def test_intro_discharges_each_half_from_the_other_proof(self):
        # P <-> P, from two copies of the assumption P.
        proof = IffIntro(Assumption(parse("P")), Assumption(parse("P")))
        self.assertEqual(proof.conclusion, parse("P <-> P"))
        self.assertTrue(proof.is_theorem())

    def test_elim_runs_whichever_way_the_half_it_is_given_points(self):
        """One rule, not two, and it needs no parameter to tell them apart."""
        biconditional = Assumption(parse("P <-> Q"))
        self.assertEqual(
            IffElim(biconditional, Assumption(parse("P"))).conclusion, parse("Q")
        )
        self.assertEqual(
            IffElim(biconditional, Assumption(parse("Q"))).conclusion, parse("P")
        )

    def test_elim_needs_one_half_or_the_other(self):
        self.assertRefuses(
            MismatchError, "neither half",
            IffElim, Assumption(parse("P <-> Q")), Assumption(parse("S")),
        )

    def test_elim_of_a_biconditional_of_one_sentence_with_itself(self):
        """P <-> P points both ways at once, and either reading gives P."""
        proof = IffElim(Assumption(parse("P <-> P")), Assumption(parse("P")))
        self.assertEqual(proof.conclusion, parse("P"))

    def test_elim_needs_a_biconditional(self):
        self.assertRefuses(
            ShapeError, "must conclude with a biconditional",
            IffElim, Assumption(parse("P -> Q")), Assumption(parse("P")),
        )


class TestUniversal(RuleTestCase):
    def test_elim(self):
        proof = ForallElim(Assumption(parse("Ax(Fx -> Gx)")), self.a)
        self.assertEqual(proof.conclusion, parse("Fa -> Ga"))

    def test_elim_needs_a_universal(self):
        self.assertRefuses(
            ShapeError, "universally quantified",
            ForallElim, Assumption(parse("Ex Fx")), self.a,
        )

    def test_intro_generalises_on_an_arbitrary_parameter(self):
        # Ax(Fx -> Gx), Ax Fx |- Ax Gx
        major = Assumption(parse("Ax(Fx -> Gx)"))
        minor = Assumption(parse("Ax Fx"))
        step = ImpliesElim(ForallElim(minor, self.a), ForallElim(major, self.a))
        proof = ForallIntro(step, self.a, self.x)
        self.assertEqual(proof.conclusion, parse("Ax Gx"))
        self.assertEqual(
            proof.assumptions,
            frozenset({parse("Ax(Fx -> Gx)"), parse("Ax Fx")}),
        )

    def test_intro_refuses_a_parameter_still_assumed(self):
        error = self.assertRefuses(
            ProvisoError, "not arbitrary",
            ForallIntro, Assumption(parse("Fa")), self.a, self.x,
        )
        self.assertIn("Fa", str(error))

    def test_intro_allows_it_once_the_assumption_is_discharged(self):
        discharged = ImpliesIntro(Assumption(parse("Fa")), parse("Fa"))
        proof = ForallIntro(discharged, self.a, self.x)
        self.assertEqual(proof.conclusion, parse("Ax(Fx -> Fx)"))
        self.assertTrue(proof.is_theorem())

    def test_identity_is_reflexive(self):
        # |- Ax x=x, the proviso holding vacuously over an empty As.
        proof = ForallIntro(EqualityIntro(self.a), self.a, self.x)
        self.assertEqual(proof.conclusion, parse("Ax x=x"))
        self.assertTrue(proof.is_theorem())

    def test_intro_refuses_to_capture(self):
        # Nothing is left assumed, so arbitrariness holds; but a sits
        # inside the scope of a quantifier on x already, and abstracting
        # it would bind it there rather than at the front.
        theorem = ImpliesIntro(Assumption(parse("Ax Rxa")), parse("Ax Rxa"))
        self.assertEqual(theorem.assumptions, frozenset())
        self.assertRefuses(
            ProvisoError, "capture", ForallIntro, theorem, self.a, self.x,
        )


class TestExistential(RuleTestCase):
    def test_intro_verifies_the_conclusion_it_is_offered(self):
        # Raa gives Ex Rxa and Ex Rxx alike; the premise does not say which.
        premise = Assumption(parse("Raa"))
        self.assertEqual(
            ExistsIntro(premise, parse("Ex Rxa")).conclusion, parse("Ex Rxa")
        )
        self.assertEqual(
            ExistsIntro(premise, parse("Ex Rax")).conclusion, parse("Ex Rax")
        )
        self.assertEqual(
            ExistsIntro(premise, parse("Ex Rxx")).conclusion, parse("Ex Rxx")
        )

    def test_intro_refuses_an_unrelated_existential(self):
        self.assertRefuses(
            MismatchError, "with a constant put for",
            ExistsIntro, Assumption(parse("Raa")), parse("Ex Rxb"),
        )

    def test_intro_with_the_parameter_named(self):
        premise = Assumption(parse("Fa"))
        self.assertEqual(
            ExistsIntro(premise, parse("Ex Fx"), self.a).conclusion, parse("Ex Fx")
        )
        error = self.assertRefuses(
            MismatchError, "putting b for x",
            ExistsIntro, premise, parse("Ex Fx"), self.b,
        )
        self.assertIn("Fb", str(error))

    def test_intro_needs_an_existential(self):
        self.assertRefuses(
            ShapeError, "existentially quantified",
            ExistsIntro, Assumption(parse("Fa")), parse("Ax Fx"),
        )

    def test_intro_over_a_variable_that_binds_nothing(self):
        self.assertEqual(
            ExistsIntro(Assumption(parse("P")), parse("Ex P")).conclusion,
            parse("Ex P"),
        )
        self.assertRefuses(
            MismatchError, "binds nothing",
            ExistsIntro, Assumption(parse("Q")), parse("Ex P"),
        )

    def test_elim(self):
        # Ex Fx, Ax(Fx -> Gx) |- Ex Gx
        major = Assumption(parse("Ax(Fx -> Gx)"))
        instance = Assumption(parse("Fa"))
        step = ImpliesElim(instance, ForallElim(major, self.a))
        claimed = ExistsIntro(step, parse("Ex Gx"), self.a)
        proof = ExistsElim(Assumption(parse("Ex Fx")), claimed, self.a)
        self.assertEqual(proof.conclusion, parse("Ex Gx"))
        self.assertEqual(
            proof.assumptions,
            frozenset({parse("Ex Fx"), parse("Ax(Fx -> Gx)")}),
        )

    def test_elim_needs_an_existential(self):
        self.assertRefuses(
            ShapeError, "existentially quantified",
            ExistsElim, Assumption(parse("Ax Fx")), Assumption(parse("P")), self.a,
        )

    def test_elim_refuses_a_parameter_in_the_existential(self):
        self.assertRefuses(
            ProvisoError, "not fresh",
            ExistsElim,
            Assumption(parse("Ex Rxa")),
            Assumption(parse("P")),
            self.a,
        )

    def test_elim_refuses_a_parameter_in_the_conclusion(self):
        # The proviso reference/NDrules.pdf omits.  Without it this is a
        # derivation of Ex Fx |- Fa.
        error = self.assertRefuses(
            ProvisoError, "occurs in the conclusion",
            ExistsElim,
            Assumption(parse("Ex Fx")),
            Assumption(parse("Fa")),
            self.a,
        )
        self.assertEqual(error.rule_name, "∃Elim")

    def test_elim_refuses_a_parameter_in_another_open_assumption(self):
        step = ImpliesElim(Assumption(parse("Ha")), Assumption(parse("Ha -> P")))
        self.assertRefuses(
            ProvisoError, "undischarged assumption",
            ExistsElim, Assumption(parse("Ex Fx")), step, self.a,
        )

    def test_an_existential_contradicts_the_universal_denial(self):
        # Ex Fx |- ~Ax ~Fx
        denial = Assumption(parse("Ax ~Fx"))
        instance = Assumption(parse("Fa"))
        negated = ForallElim(denial, self.a)
        contradiction = NotIntro(instance, negated, parse("Ax ~Fx"))
        proof = ExistsElim(Assumption(parse("Ex Fx")), contradiction, self.a)
        self.assertEqual(proof.conclusion, parse("~Ax ~Fx"))
        self.assertEqual(proof.assumptions, frozenset({parse("Ex Fx")}))


class TestIdentity(RuleTestCase):
    def test_intro(self):
        proof = EqualityIntro(self.a)
        self.assertEqual(proof.conclusion, parse("a=a"))
        self.assertTrue(proof.is_theorem())

    def test_elim_replaces_some_occurrences(self):
        identity = Assumption(parse("a=b"))
        premise = Assumption(parse("Raa"))
        for target in ("Rab", "Rba", "Rbb", "Raa"):
            with self.subTest(target=target):
                self.assertEqual(
                    EqualityElim(identity, premise, parse(target)).conclusion,
                    parse(target),
                )

    def test_elim_runs_in_the_other_direction_too(self):
        """One rule, not two: the conclusion says which way it was read."""
        identity = Assumption(parse("a=b"))
        premise = Assumption(parse("Rbb"))
        for target in ("Rab", "Rba", "Raa", "Rbb"):
            with self.subTest(target=target):
                self.assertEqual(
                    EqualityElim(identity, premise, parse(target)).conclusion,
                    parse(target),
                )

    def test_elim_reads_either_direction_off_the_same_two_subproofs(self):
        """a=b over Rab reaches Raa by one reading and Rbb by the other."""
        identity, premise = Assumption(parse("a=b")), Assumption(parse("Rab"))
        self.assertEqual(
            EqualityElim(identity, premise, parse("Rbb")).conclusion, parse("Rbb")
        )
        self.assertEqual(
            EqualityElim(identity, premise, parse("Raa")).conclusion, parse("Raa")
        )

    def test_elim_refuses_an_unrelated_conclusion(self):
        self.assertRefuses(
            MismatchError, "occurrences of a replaced by b, or of b by a",
            EqualityElim,
            Assumption(parse("a=b")),
            Assumption(parse("Raa")),
            parse("Rac"),
        )

    def test_elim_needs_an_identity(self):
        self.assertRefuses(
            ShapeError, "must conclude with an identity",
            EqualityElim,
            Assumption(parse("P")),
            Assumption(parse("Q")),
            parse("Q"),
        )

    def test_identity_is_symmetric(self):
        # a=b |- b=a, by replacing the first a in a=a.
        proof = EqualityElim(
            Assumption(parse("a=b")), EqualityIntro(self.a), parse("b=a")
        )
        self.assertEqual(proof.conclusion, parse("b=a"))
        self.assertEqual(proof.assumptions, frozenset({parse("a=b")}))

    def test_elim_reaches_inside_connectives_and_quantifiers(self):
        identity = Assumption(parse("a=b"))
        premise = Assumption(parse("Fa & Ax(Gx -> Rxa)"))
        self.assertEqual(
            EqualityElim(
                identity, premise, parse("Fb & Ax(Gx -> Rxa)")
            ).conclusion,
            parse("Fb & Ax(Gx -> Rxa)"),
        )


class TestReplacesSome(RuleTestCase):
    """The partial-replacement check the identity rules verify against."""

    def test_every_subset_of_occurrences(self):
        source = parse("Raa")
        for target in ("Raa", "Rab", "Rba", "Rbb"):
            self.assertTrue(
                _replaces_some(source, parse(target), self.a, self.b), target
            )

    def test_it_does_not_replace_in_the_wrong_direction(self):
        self.assertFalse(
            _replaces_some(parse("Rab"), parse("Raa"), self.a, self.b)
        )

    def test_shape_must_be_preserved(self):
        self.assertFalse(_replaces_some(parse("Fa"), parse("Ga"), self.a, self.b))
        self.assertFalse(
            _replaces_some(parse("P & Q"), parse("P | Q"), self.a, self.b)
        )
        self.assertFalse(
            _replaces_some(parse("Ax Fx"), parse("Ay Fy"), self.a, self.b)
        )

    def test_it_descends_through_every_construct(self):
        self.assertTrue(
            _replaces_some(
                parse("~(Fa <-> Ex(Gx & Rxa)) & a=a"),
                parse("~(Fb <-> Ex(Gx & Rxa)) & a=b"),
                self.a,
                self.b,
            )
        )


if __name__ == "__main__":
    unittest.main()
