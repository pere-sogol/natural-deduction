"""Tests for ndweb.codec: saving, loading and sharing a document."""

import unittest

from nd.formula import declared_arities, reset_arities
from nd.parser import parse

from ndweb.codec import (
    decode,
    encode,
    from_fragment,
    from_json,
    to_fragment,
    to_json,
)
from ndweb.derivation import Card, Document, Goal
from ndweb.exercises import EXERCISES, solution


class CodecTestCase(unittest.TestCase):
    def setUp(self):
        reset_arities()

    def document(self, key):
        root = solution(key)
        return Document(
            goal=parse("P"), premises=(), cards=(Card(root, 120, 40),), next_id=500
        )


class TestRoundTrip(CodecTestCase):
    def test_every_recorded_solution_survives_the_trip(self):
        """The same discipline as parse(str(f)) == f, one level up."""
        for exercise in EXERCISES:
            reset_arities()
            document = self.document(exercise.key)
            self.assertEqual(decode(encode(document)), document, exercise.key)

    def test_json_and_back(self):
        document = self.document("russell")
        self.assertEqual(from_json(to_json(document)), document)

    def test_a_url_fragment_and_back(self):
        document = self.document("russell")
        fragment = to_fragment(document)
        self.assertNotIn("=", fragment)
        self.assertEqual(from_fragment(fragment), document)

    def test_a_whole_proof_fits_in_a_link(self):
        """Sharing has to work for the biggest thing in the library."""
        self.assertLess(len(to_fragment(self.document("russell"))), 1500)

    def test_an_empty_document_round_trips(self):
        self.assertEqual(decode(encode(Document())), Document())

    def test_slots_survive_as_slots(self):
        document = Document(
            goal=parse("P"), cards=(Card(Goal(3, parse("P")), 8, 9),), next_id=4
        )
        back = decode(encode(document))
        self.assertIsInstance(back.cards[0].node, Goal)
        self.assertEqual(back.cards[0].node.id, 3)
        self.assertEqual((back.cards[0].x, back.cards[0].y), (8, 9))

    def test_a_blank_slot_survives_as_blank(self):
        """A sheet may be saved mid-thought, with nothing written in yet."""
        document = Document(cards=(Card(Goal(3)),), next_id=4)
        self.assertEqual(decode(encode(document)), document)


class TestArityIsolation(CodecTestCase):
    def test_loading_forgets_what_was_being_edited_before(self):
        """A document is self-contained; last session's letters do not bind."""
        parse("Rxy")
        self.assertEqual(declared_arities()["R"], 2)
        document = Document(goal=parse("P"), premises=(parse("Fa"),))
        raw = encode(document)
        reset_arities()
        parse("Rxyz")
        self.assertEqual(declared_arities()["R"], 3)
        decode(raw)
        self.assertNotIn("R", declared_arities())
