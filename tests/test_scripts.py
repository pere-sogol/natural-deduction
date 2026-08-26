"""End to end: known proofs, built both ways.

Forwards, the recorded solutions are realised and checked against the
sequent they claim.  Backwards, the same theorems are built through
:class:`ndweb.session.Session` with the moves a student actually makes:
put a rule on a slot, write a sentence in a premise, name a parameter.
Nothing else -- no rule is told in advance what it will need.

That half is what really exercises :mod:`ndweb.unify`, because it runs it
on whole proofs rather than a rule at a time, and because every sentence
not written below is one the sheet had to work out for itself.
"""

import unittest

from nd.formula import reset_arities
from nd.parser import parse

from ndweb.exercises import EXERCISES, solution
from ndweb.realise import realise
from ndweb.session import Session

#: Backward constructions, as the moves that make them.
#:
#: ``at`` names the slot by what it reads, the way a student picks one out;
#: ``premises`` writes into a premise slot by index; ``params`` names a
#: parameter.  Everything else on each block is worked out.
BACKWARD_SCRIPTS = {
    "identity": [
        {"at": "P → P", "rule": "→Intro"},
        {"at": "P", "rule": "Assumption"},
    ],
    "double-negation": [
        {"at": "¬¬P → P", "rule": "→Intro"},
        {"at": "P", "rule": "¬Elim", "premises": {0: "~P"}},
        {"at": "¬P", "rule": "Assumption"},
        {"at": "¬¬P", "rule": "Assumption"},
    ],
    "modus-tollens": [
        {"at": "(P → Q) → ¬Q → ¬P", "rule": "→Intro"},
        {"at": "¬Q → ¬P", "rule": "→Intro"},
        {"at": "¬P", "rule": "¬Intro", "premises": {0: "Q"}},
        {"at": "Q", "rule": "→Elim", "premises": {0: "P"}},
        {"at": "P", "rule": "Assumption"},
        {"at": "P → Q", "rule": "Assumption"},
        {"at": "¬Q", "rule": "Assumption"},
    ],
    "excluded-middle": [
        {"at": "P ∨ ¬P", "rule": "¬Elim", "premises": {0: "P | ~P"}},
        {"at": "P ∨ ¬P", "rule": "∨Intro", "premises": {0: "~P"}},
        {"at": "¬P", "rule": "¬Intro", "premises": {0: "P | ~P"}},
        {"at": "P ∨ ¬P", "rule": "∨Intro", "premises": {0: "P"}},
        {"at": "P", "rule": "Assumption"},
        {"at": "¬(P ∨ ¬P)", "rule": "Assumption"},
        {"at": "¬(P ∨ ¬P)", "rule": "Assumption"},
    ],
    "self-identity": [
        {"at": "∀x x=x", "rule": "∀Intro", "params": {"constant": "a"}},
        {"at": "a=a", "rule": "=Intro"},
    ],
    "distribute": [
        {"at": "∀x Gx", "rule": "∀Intro", "params": {"constant": "a"}},
        {"at": "Ga", "rule": "→Elim", "premises": {0: "Fa"}},
        {"at": "Fa", "rule": "∀Elim", "premises": {0: "Ax Fx"}},
        {"at": "∀x Fx", "rule": "Assumption"},
        {"at": "Fa → Ga", "rule": "∀Elim", "premises": {0: "Ax(Fx -> Gx)"}},
        {"at": "∀x(Fx → Gx)", "rule": "Assumption"},
    ],
}


class TestForwards(unittest.TestCase):
    def test_every_recorded_solution_proves_its_sequent(self):
        for exercise in EXERCISES:
            reset_arities()
            realisation = realise(solution(exercise.key))
            self.assertTrue(realisation.complete, exercise.key)
            self.assertTrue(
                realisation.proof.proves(
                    parse(exercise.goal),
                    frozenset(parse(p) for p in exercise.premises),
                ),
                exercise.key,
            )

    def test_a_drawn_proof_matches_the_book(self):
        """One pinned drawing, so a change to placement is noticed here too."""
        reset_arities()
        realisation = realise(solution("distribute"))
        self.assertEqual(
            str(realisation.proof),
            "\n".join([
                "∀x Fx      ∀x(Fx → Gx)",
                "───── ∀E   ─────────── ∀E",
                " Fa          Fa → Ga",
                " ─────────────────── →E",
                "         Ga",
                "       ───── ∀I",
                "       ∀x Gx",
            ]),
        )


class TestBackwards(unittest.TestCase):
    """Every theorem above, built with nothing but slots and sentences."""

    def _nodes(self, state):
        found = []

        def descend(node):
            for child in node["premises"]:
                descend(child)
            found.append(node)

        for card in state["cards"]:
            descend(card["tree"])
        return found

    def _slot(self, state, sentence):
        """The empty slot reading ``sentence``, as a student would point."""
        for node in self._nodes(state):
            if node["kind"] == "slot" and node["conclusion"]["text"] == sentence:
                return node["id"]
        raise AssertionError(
            "no slot reading {0!r}; the open ones read {1}".format(
                sentence,
                [n["conclusion"]["text"] for n in self._nodes(state)
                 if n["kind"] == "slot"],
            )
        )

    def _children(self, state, node_id):
        for node in self._nodes(state):
            if node["id"] == node_id:
                return [child["id"] for child in node["premises"]]
        raise AssertionError("no node {0}".format(node_id))

    def _play(self, key):
        session = Session()
        state = session.dispatch({"op": "exercise", "key": key})
        for move in BACKWARD_SCRIPTS[key]:
            at = self._slot(state, move["at"])
            state = session.dispatch(
                {"op": "place", "rule": move["rule"], "slot": at})
            children = self._children(state, at)
            for index, text in sorted(move.get("premises", {}).items()):
                state = session.dispatch(
                    {"op": "set", "node": children[index], "text": text})
            for name, text in sorted(move.get("params", {}).items()):
                state = session.dispatch(
                    {"op": "param", "node": at, "name": name, "text": text})
        return state

    def test_the_scripts_reach_their_theorems(self):
        for key in BACKWARD_SCRIPTS:
            reset_arities()
            state = self._play(key)
            self.assertEqual(state["openSlots"], [],
                             "{0}: slots left empty".format(key))
            self.assertTrue(state["solved"], "{0}: {1}".format(key, state["notice"]))

    def test_no_step_is_left_complaining(self):
        """A finished sheet should be silent, not merely correct."""
        for key in BACKWARD_SCRIPTS:
            reset_arities()
            state = self._play(key)
            for node in self._nodes(state):
                self.assertEqual(node["message"], "",
                                 "{0}: {1}".format(key, node["message"]))

    def test_both_directions_reach_the_same_theorem(self):
        for key in BACKWARD_SCRIPTS:
            reset_arities()
            state = self._play(key)
            built = [card for card in state["cards"]
                     if card["root"] == state["provedBy"]][0]
            reset_arities()
            forwards = realise(solution(key))
            self.assertEqual(built["conclusion"],
                             str(forwards.proof.conclusion), key)
            self.assertEqual(built["open"],
                             sorted(str(f) for f in forwards.proof.assumptions), key)
