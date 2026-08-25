"""The editor's one entry point.

The browser sends an action and gets the whole state back.  There are no
deltas: a set proof is tens of elements, so re-setting it costs less than
the bookkeeping needed to avoid re-setting it, and a front end that cannot
get out of step with the model is worth more than the microseconds.

Nothing here raises at the caller.  A refusal -- a rule that does not
apply, a formula that will not parse, a parameter that breaks a proviso --
comes back inside the state as something to show the student, because all
of those are ordinary events in the course of building a proof rather
than faults.

The operations are deliberately few and general.  There is no "apply this
rule to that goal" and no dialogue asking for what a rule needs before it
may be used: a rule is *put down*, anywhere, and then written into.
Everything that used to be asked for in advance -- which sentence, which
parameter, which of two premises -- is a slot on the block, and
:mod:`ndweb.unify` fills in whichever of them the others settle.  What is
left is: put a block down, write in a slot, join two blocks, take them
apart again.

Undo is a list of documents and an index.  Documents are immutable and
share structure, so keeping every past state costs almost nothing, and
stepping between them cannot go wrong the way replaying a journal of
edits can.
"""

from __future__ import annotations

from dataclasses import replace
from typing import Any, Dict, List, Optional

from nd.formula import Constant, Formula, FormulaError, Variable, reset_arities
from nd.parser import ParseError, parse, parse_term
from nd.proofs import rule

from ndweb import codec
from ndweb.derivation import (
    Binding,
    Card,
    Document,
    Goal,
    Node,
    Step,
    arity,
    card_of,
    detach_node,
    find,
    substitute_node,
)
from ndweb.exercises import EXERCISES, exercise
from ndweb.refine import RefineError
from ndweb.unify import solve
from ndweb.view import view

__all__ = ["Session"]

#: How many past states to keep.  Generous, because they share structure.
DEPTH = 200

#: Where a card lands when nobody said where.
_DEFAULT = (60, 60)


class Session:
    """One editing session: a history of documents and where we are in it."""

    def __init__(self) -> None:
        self.history: List[Document] = [Document()]
        self.index = 0
        self.focus: Optional[int] = None

    # -- state ------------------------------------------------------------

    @property
    def document(self) -> Document:
        return self.history[self.index]

    def _commit(self, document: Document) -> None:
        self.history = self.history[: self.index + 1][-DEPTH:]
        self.history.append(document)
        self.index = len(self.history) - 1

    def state(self, notice: str = "") -> Dict[str, Any]:
        found = view(self.document, self.focus, notice)
        found["canUndo"] = self.index > 0
        found["canRedo"] = self.index < len(self.history) - 1
        found["revision"] = self.index
        found["exercises"] = [
            {"key": e.key, "title": e.title, "sequent": e.sequent,
             "premises": list(e.premises), "goal": e.goal, "note": e.note}
            for e in EXERCISES
        ]
        found["fragment"] = codec.to_fragment(self.document)
        return found

    # -- the one call the browser makes -----------------------------------

    def dispatch(self, action: Dict[str, Any]) -> Dict[str, Any]:
        operation = (action or {}).get("op", "view")
        handler = getattr(self, "_op_" + operation.replace("-", "_"), None)
        if handler is None:
            return self.state(notice="unknown action {0!r}".format(operation))
        try:
            return handler(action)
        except (ParseError, FormulaError) as error:
            return self.state(notice=str(error).split("\n")[0])
        except RefineError as error:
            return self.state(notice=error.message)
        except KeyError as error:
            return self.state(notice="there is no rule called {0}".format(error))

    # -- starting and loading ---------------------------------------------

    def _op_view(self, action):
        return self.state()

    def _op_new(self, action):
        """Set the sequent, and lay the premises out as blocks to build on."""
        reset_arities()
        premises = tuple(parse(text) for text in action.get("premises") or ())
        goal_text = str(action.get("goal") or "").strip()
        goal = parse(goal_text) if goal_text else None

        document = Document(goal=goal, premises=premises)
        left = 60
        for premise in premises:
            node_id, document = document.fresh()
            step = Step(node_id, "Assumption", (), (), premise)
            document = replace(document, cards=document.cards + (
                Card(step, left, 60),))
            left += 200
        if goal is not None:
            node_id, document = document.fresh()
            document = replace(document, cards=document.cards + (
                Card(Goal(node_id, goal), max(left, 60), 300),))
            self.focus = node_id
        self._commit(document)
        return self.state()

    def _op_exercise(self, action):
        chosen = exercise(action["key"])
        return self._op_new({"goal": chosen.goal, "premises": list(chosen.premises)})

    def _op_clear(self, action):
        """Sweep the sheet, keeping the sequent."""
        document = self.document
        self._commit(Document(goal=document.goal, premises=document.premises,
                              next_id=document.next_id))
        self.focus = None
        return self.state()

    def _op_load(self, action):
        self._commit(codec.decode(action["document"]))
        self.focus = None
        return self.state()

    def _op_load_fragment(self, action):
        self._commit(codec.from_fragment(action["fragment"]))
        self.focus = None
        return self.state()

    # -- moving about ------------------------------------------------------

    def _op_focus(self, action):
        self.focus = action.get("node")
        return self.state()

    def _op_undo(self, action):
        if self.index > 0:
            self.index -= 1
        return self.state()

    def _op_redo(self, action):
        if self.index < len(self.history) - 1:
            self.index += 1
        return self.state()

    def _op_move(self, action):
        """Where a card sits.  Changes nothing about what it proves."""
        document = self.document
        root = int(action["root"])
        cards = tuple(
            replace(card, x=int(action.get("x", card.x)),
                    y=int(action.get("y", card.y)))
            if card.node.id == root else card
            for card in document.cards
        )
        self._commit(replace(document, cards=cards))
        return self.state()

    # -- putting a block down ----------------------------------------------

    def _op_place(self, action):
        """Put a rule on the sheet, with every slot empty.

        Dropped on a slot it goes into it, inheriting whatever that slot
        was going to say; dropped on the sheet it starts a card of its own.
        Neither asks for anything first -- what the rule needs shows as
        slots on the block, and most of them fill themselves in.
        """
        rule_name = action["rule"]
        rule(rule_name)  # KeyError here is caught in dispatch
        document = self.document
        count = arity(rule_name)

        into = action.get("slot")
        step_id, document = document.fresh()
        child_ids, document = document.spend(count)
        children = tuple(Goal(i) for i in child_ids)

        if into is None:
            step = Step(step_id, rule_name, children)
            document = replace(document, cards=document.cards + (
                Card(step, int(action.get("x", _DEFAULT[0])),
                     int(action.get("y", _DEFAULT[1]))),))
            self.focus = step_id
            self._commit(document)
            return self.state()

        slot = find(document, int(into))
        if not isinstance(slot, Goal):
            return self.state(notice="that is not an empty slot")
        text = str(action.get("text") or "").strip()
        claim = parse(text) if text else slot.target
        step = Step(slot.id, rule_name, children, (), claim)
        self._commit(self._replace(document, slot.id, step))
        self.focus = children[0].id if children else slot.id
        return self.state()

    # -- writing in a slot -------------------------------------------------

    def _op_set(self, action):
        """Write a sentence into a slot, or on the line under a bar."""
        document = self.document
        node = find(document, int(action["node"]))
        if node is None:
            return self.state(notice="no such slot")
        text = str(action.get("text") or "").strip()
        formula = parse(text) if text else None

        if isinstance(node, Goal):
            changed = replace(node, target=formula)
        else:
            changed = replace(node, claim=formula)
        self._commit(self._replace(document, node.id, changed))
        self.focus = node.id
        return self.state()

    def _op_param(self, action):
        """Write one of the values a rule needs besides its premises."""
        document = self.document
        node = find(document, int(action["node"]))
        if not isinstance(node, Step):
            return self.state(notice="only a rule takes parameters")
        name = str(action["name"])
        text = str(action.get("text") or "").strip()
        kept = tuple(b for b in node.params if b.name != name)
        if text:
            kept = kept + (Binding(name, _value(node.rule, name, text)),)
        self._commit(self._replace(document, node.id, replace(node, params=kept)))
        self.focus = node.id
        return self.state()

    # -- joining and parting -----------------------------------------------

    def _op_attach(self, action):
        """Drop one card into a slot on another.

        Nothing is checked here beyond the two existing.  Whether the block
        proves what the slot wanted is the checker's business, and it says
        so on the bar; refusing the join would only leave the student
        holding a block with nowhere to put it and no explanation.
        """
        document = self.document
        slot = find(document, int(action["slot"]))
        source = int(action["source"])
        card = next((c for c in document.cards if c.node.id == source), None)
        if not isinstance(slot, Goal):
            return self.state(notice="that is not an empty slot")
        if card is None:
            return self.state(notice="that block is not on the sheet")
        if any(node.id == slot.id for node in _nodes(card.node)):
            return self.state(notice="a block cannot be dropped into itself")

        document = replace(document, cards=tuple(
            c for c in document.cards if c.node.id != source))
        self._commit(self._replace(document, slot.id, card.node))
        self.focus = card.node.id
        return self.state()

    def _op_detach(self, action):
        """Pull a branch off, leaving a slot that remembers what it said."""
        document = self.document
        node_id = int(action["node"])
        holder = card_of(document, node_id)
        if holder is None:
            return self.state(notice="no such block")
        if holder.node.id == node_id:
            return self.state(notice="that block is already loose")

        # The slot left behind should say what the branch was supplying,
        # which for a block built upwards is worked out rather than written.
        known = solve(holder.node, frozenset(document.premises)).formula(node_id)
        left, taken = detach_node(holder.node, node_id, known)
        if taken is None:
            return self.state(notice="no such block")
        cards = tuple(replace(c, node=left) if c is holder else c
                      for c in document.cards)
        cards = cards + (Card(taken, int(action.get("x", _DEFAULT[0])),
                              int(action.get("y", _DEFAULT[1]))),)
        self._commit(replace(document, cards=cards))
        self.focus = taken.id
        return self.state()

    def _op_delete(self, action):
        """Throw a block away.  A branch leaves an empty slot behind."""
        document = self.document
        node_id = int(action["node"])
        if any(card.node.id == node_id for card in document.cards):
            self._commit(replace(document, cards=tuple(
                c for c in document.cards if c.node.id != node_id)))
            self.focus = None
            return self.state()
        node = find(document, node_id)
        if node is None:
            return self.state(notice="no such block")
        self._commit(self._replace(document, node_id, Goal(node_id)))
        self.focus = node_id
        return self.state()

    # -- helpers -----------------------------------------------------------

    def _replace(self, document: Document, node_id: int, node: Node) -> Document:
        cards = tuple(
            replace(card, node=substitute_node(card.node, node_id, node))
            for card in document.cards
        )
        return replace(document, cards=cards)


def _nodes(node: Node):
    from ndweb.derivation import walk

    return list(walk(node))


def _value(rule_name: str, name: str, text):
    """A parameter's text as the sort of thing the rule wants."""
    if isinstance(text, (Formula, Constant, Variable)):
        return text
    kinds = dict((p.name, p.kind) for p in rule(rule_name).parameters)
    kind = kinds.get(name, "formula")
    if kind == "formula":
        return parse(str(text))
    term = parse_term(str(text))
    if kind == "constant" and not isinstance(term, Constant):
        raise RefineError(
            "{0} must be a constant (a to t); {1} is a variable".format(name, term)
        )
    if kind == "variable" and not isinstance(term, Variable):
        raise RefineError(
            "{0} must be a variable (u to z); {1} is a constant".format(name, term)
        )
    return term
