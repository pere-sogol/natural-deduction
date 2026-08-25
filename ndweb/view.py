"""The whole state of the sheet, as data the browser can set.

Everything the front end draws comes from here, so that the front end can
stay ignorant of the logic: it never parses a formula, never knows which
rules take parameters, never decides whether a step is sound.  It sets
type and forwards clicks.

Nothing carries a position except a card, and a card's position is the
student's own arrangement rather than anything computed.  Inside a block
there are no coordinates at all: :mod:`ndweb.typeset` emits the nesting
and the browser measures the text, so a sentence growing longer widens its
own bar and nothing else moves.
"""

from __future__ import annotations

from typing import Any, Dict, List, Optional

from nd.formula import declared_arities

from ndweb.catalogue import catalogue
from ndweb.derivation import Document, Goal, Node, find
from ndweb.realise import contexts, realise
from ndweb.refine import BACKWARD, Context, RefineError, fields
from ndweb.typeset import card, schema
from ndweb.unify import solve

__all__ = ["view", "palette"]


def palette(target=None, available=frozenset()) -> List[Dict[str, Any]]:
    """Every rule, with its figure and -- if a slot is in hand -- a hint.

    Every rule stays droppable whatever is focused.  On a sandbox that is
    the point: a rule may be put down to be filled in later, or to be built
    upon from above, and refusing the ones that cannot immediately close
    the selected slot would make most of the table dead most of the time.
    So a rule that does not fit is *marked*, with the reason it does not,
    and dropped all the same.
    """
    rows = []
    for info in catalogue():
        fits, why = True, ""
        if target is not None:
            try:
                fields(info.name, target, Context(available=available))
            except RefineError as error:
                fits, why = False, error.message
        rows.append({
            "name": info.name,
            "label": info.label,
            "subproofs": info.subproofs,
            "group": info.group,
            "connective": info.connective,
            "summary": info.summary,
            "caveat": info.caveat,
            "backward": BACKWARD.get(info.name, ""),
            "schema": schema(info.name),
            "fits": fits,
            "why": why,
        })
    return rows


def view(
    document: Document, focus: Optional[int] = None, notice: str = ""
) -> Dict[str, Any]:
    """Everything the browser needs to set the editor once."""
    base = frozenset(document.premises)
    cards = [card(entry, base) for entry in document.cards]

    proved_by = None
    if document.goal is not None:
        for entry, drawn in zip(document.cards, cards):
            found = realise(entry.node, solve(entry.node, base))
            if found.proof is not None and found.proof.proves(
                document.goal, document.premises
            ):
                proved_by = entry.node.id
                break

    where = contexts(document)
    focused = find(document, focus) if focus is not None else None
    target = None
    if focused is not None:
        target = solve_target(document, focused, base)

    open_slots: List[int] = []
    for drawn in cards:
        open_slots.extend(drawn["openSlots"])

    return {
        "goal": None if document.goal is None else str(document.goal),
        "premises": [str(premise) for premise in document.premises],
        "sequent": _sequent(document),
        "solved": proved_by is not None,
        "provedBy": proved_by,
        "openSlots": open_slots,
        "focus": focus,
        "cards": cards,
        "palette": palette(target, where.get(focus, frozenset())),
        "contexts": dict(
            (str(node_id), sorted(str(f) for f in formulae))
            for node_id, formulae in where.items()
        ),
        "signature": sorted(declared_arities().items()),
        "notice": notice,
    }


def solve_target(document: Document, node: Node, base):
    """What the focused node is understood to conclude, if anything."""
    for entry in document.cards:
        found = solve(entry.node, base).formula(node.id)
        if found is not None:
            return found
    return node.target if isinstance(node, Goal) else None


def _sequent(document: Document) -> str:
    if document.goal is None:
        return ""
    left = ", ".join(str(premise) for premise in document.premises)
    return (
        "{0} ⊢ {1}".format(left, document.goal)
        if left
        else "⊢ {0}".format(document.goal)
    )
