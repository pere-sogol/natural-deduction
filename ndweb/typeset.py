"""Setting a proof, rather than drawing it on a grid.

:func:`nd.render.layout` puts every sentence at an integer column and row,
which is exactly right for a terminal and wrong for a page.  It forces one
width on every glyph, so the whole figure hangs on the reader happening to
have a monospace font containing ``∀ ∃ → ↔``; and it fixes the widths in
Python, so a proof cannot reflow when the window changes or when a longer
sentence appears three branches away.

A proof tree does not actually need any of that.  Each inference is a row
of premises, a rule below them, and a conclusion centred under it, which
is a nesting of boxes -- so this module emits the nesting and lets the
browser measure the text, the way ``bussproofs`` lets TeX do it.  Every
box then takes the width of what is in it and the tree assembles itself.

What is *not* given up is the book's discharge numbering, which is
genuinely subtle -- numbers rise as the eye travels down, a step that
closes nothing gets none, and one number can mark several leaves.  Rather
than write that a second time, ``layout`` is still run and its numbers are
read off it: the placement is thrown away and the annotation kept.

Sentences are emitted as classified pieces rather than as text, so that
predicate letters, terms and connectives can be set differently -- italic
for the letters, upright with proper space around the connectives.  The
classifier reads the printed sentence rather than the formula, which
sounds backwards and is not: it guarantees that what is set is exactly
what :meth:`nd.formula.Formula.__str__` produced, brackets and all, and
that is the string the parser will read back.
"""

from __future__ import annotations

from typing import Any, Dict, List, Optional

from nd.formula import Formula
from nd.proofs import rule
from nd.render import layout

from ndweb.assumptions import rests
from ndweb.attempt import UNFINISHED
from ndweb.catalogue import SCHEMA
from ndweb.derivation import Goal, Node, Step, parameters
from ndweb.realise import Realisation, realise
from ndweb.shadow import Shadow, Unknown, shadow
from ndweb.unify import Solved, solve

__all__ = ["pieces", "typeset", "card", "schema", "rest"]

_BINARY = "∧∨→↔="
_QUANTIFIERS = "∀∃"
_GREEK = "φψχ"


def pieces(text: str) -> List[Dict[str, str]]:
    """One printed sentence, cut into classified pieces.

    ``Rxy`` is a predicate letter and two terms, ``Loves(a, b)`` a name and
    two terms; the difference is decided the way the parser decides it, by
    whether a bracket follows.

    Nothing is thrown away.  A space that only separates a connective from
    its arguments is *marked* rather than dropped -- the space around a
    connective is a matter of setting rather than of the string, and the
    stylesheet gives it the right size -- and the underscore of a subscript
    is a piece of its own.  So the pieces put back together are the printed
    sentence exactly, character for character, which is the invariant worth
    having: whatever is set can be read back by the parser.
    """
    found: List[Dict[str, str]] = []
    index, length = 0, len(text)
    while index < length:
        char = text[index]
        if char == " ":
            found.append({"c": "gap", "t": " "})
            index += 1
        elif char in "()":
            found.append({"c": "paren", "t": char})
            index += 1
        elif char == ",":
            found.append({"c": "punct", "t": char})
            index += 1
        elif char == "¬":
            found.append({"c": "neg", "t": char})
            index += 1
        elif char in _QUANTIFIERS:
            found.append({"c": "quant", "t": char})
            index += 1
        elif char in _BINARY:
            found.append({"c": "op", "t": char})
            index += 1
        elif char in _GREEK:
            found.append({"c": "meta", "t": char})
            index += 1
        elif char.isupper():
            run = index
            while run < length and text[run].isalpha():
                run += 1
            if run < length and text[run] == "(":
                found.append({"c": "pred", "t": text[index:run]})
                index = run
            else:
                found.append({"c": "pred", "t": char})
                index += 1
        elif char.isalpha():
            found.append({"c": "var" if char in "uvwxyz" else "const", "t": char})
            index += 1
            if index + 1 < length and text[index] == "_" and text[index + 1].isdigit():
                digits = index + 1
                while digits < length and text[digits].isdigit():
                    digits += 1
                found.append({"c": "under", "t": "_"})
                found.append({"c": "sub", "t": text[index + 1 : digits]})
                index = digits
        else:
            found.append({"c": "other", "t": char})
            index += 1
    return _tighten(found)


def _tighten(found: List[Dict[str, str]]) -> List[Dict[str, str]]:
    """Mark the spaces the stylesheet is going to supply itself."""
    for at, piece in enumerate(found):
        if piece["c"] != "gap":
            continue
        before = found[at - 1]["c"] if at else ""
        after = found[at + 1]["c"] if at + 1 < len(found) else ""
        if "op" in (before, after) or before == "punct":
            piece["c"] = "tight"
    return found


def _sentence(value, source: str = "derived") -> Dict[str, Any]:
    """One sentence ready to be set, however much of it is known."""
    if value is None or isinstance(value, Unknown):
        return {"text": "", "pieces": [], "source": "blank"}
    text = str(value)
    return {"text": text, "pieces": pieces(text), "source": source}


def schema(rule_name: str) -> Dict[str, Any]:
    """The rule's own figure, for the palette.

    Set by the same code that sets a real inference, so a student sees the
    shape they are about to put on the sheet rather than a picture of it.
    """
    premises, conclusion, closed = SCHEMA.get(rule_name, ((), "", ()))
    return {
        "premises": [
            {
                "conclusion": _sentence(text, "schema"),
                "discharged": None if at >= len(closed) else closed[at],
                "brackets": at < len(closed) and closed[at] is not None,
            }
            for at, text in enumerate(premises)
        ],
        "conclusion": _sentence(conclusion, "schema"),
        "label": rule(rule_name).label,
    }


# -- a whole tree ----------------------------------------------------------


def _post_order(node: Shadow) -> List[Shadow]:
    found: List[Shadow] = []
    for child in node.subproofs:
        found.extend(_post_order(child))
    found.append(node)
    return found


def typeset(
    root: Node,
    realisation: Optional[Realisation] = None,
    solved: Optional[Solved] = None,
) -> Dict[str, Any]:
    """One derivation as a nesting of inferences the browser can set."""
    if solved is None:
        solved = solve(root)
    if realisation is None:
        realisation = realise(root, solved)

    drawn = shadow(root, realisation, solved)
    placed = layout(drawn, ascii_only=True)
    order = _post_order(drawn)
    marks = dict(
        (id(node), spot.discharge) for node, spot in zip(order, placed.formulae)
    )
    inferences = [node for node in order if not node.is_leaf]
    numbers = dict(
        (id(node), _number(spot.label, node.label))
        for node, spot in zip(inferences, placed.bars)
    )

    proof = realisation.proof
    still_open = frozenset(proof.assumptions) if proof is not None else frozenset()
    return _node(drawn, realisation, solved, marks, numbers, still_open)


def _number(label: str, plain: str) -> Optional[int]:
    """``"->I, 1"`` gives 1.

    The renderer writes the rule and its discharge number as one string;
    they are taken apart here with the rule's own label rather than by
    looking for a comma, which a rule name could contain.
    """
    if label != plain and label.startswith(plain):
        rest = label[len(plain) :].lstrip(", ")
        if rest.isdigit():
            return int(rest)
    return None


def _node(
    drawn: Shadow,
    realisation: Realisation,
    solved: Solved,
    marks: Dict[int, Optional[int]],
    numbers: Dict[int, Optional[int]],
    still_open,
) -> Dict[str, Any]:
    origin = drawn.node
    node_id = origin.id if origin is not None else -1
    written = solved.is_written(node_id)
    known = None if isinstance(drawn.conclusion, Unknown) else drawn.conclusion
    sentence = _sentence(known, "written" if written else "derived")

    mark = marks.get(id(drawn))
    sentence["discharged"] = mark
    sentence["open"] = bool(
        drawn.is_leaf and mark is None and known is not None and known in still_open
    )
    sentence["slot"] = node_id

    if isinstance(origin, Goal):
        # A slot written into is assumed, and an assumption can be refused
        # -- ``Fx`` is not a sentence, so no line of a proof may be it.
        # Nothing above a slot will ever fix that, so unlike a step waiting
        # on its branches it is said rather than left to be discovered.
        refusal = realisation.failures.get(node_id)
        return {
            "id": node_id,
            "kind": "slot",
            "rule": "",
            "label": "",
            "number": None,
            "premises": [],
            "params": [],
            "conclusion": sentence,
            "status": ("blank" if known is None
                       else "slot" if refusal is None else refusal.kind),
            "message": "" if refusal is None else refusal.message,
            "detail": "" if refusal is None else refusal.detail,
            "note": "",
        }

    failure = realisation.failures.get(node_id)
    status = "ok"
    if failure is not None:
        status = "pending" if failure.kind in UNFINISHED else failure.kind
    elif node_id not in realisation.proofs:
        status = "pending"
    # A step waiting on an unfinished branch is the ordinary state of a
    # proof being built, not something to be told about.  An empty
    # parameter is drawn the same way but does get a line, because no
    # amount of work above will ever fill it in.
    message = "" if failure is None or failure.kind == "blocked" else failure.message

    return {
        "id": node_id,
        "kind": "step",
        "rule": origin.rule,
        "label": drawn.label,
        "number": numbers.get(id(drawn)),
        "premises": [
            _node(child, realisation, solved, marks, numbers, still_open)
            for child in drawn.subproofs
        ],
        "params": _params(origin, solved),
        "conclusion": sentence,
        "status": status,
        "message": message,
        "detail": "" if failure is None else failure.detail,
        "note": "  ".join(solved.notes.get(node_id, ())),
    }


def _params(step: Step, solved: Solved) -> List[Dict[str, Any]]:
    """The slots for what a rule needs besides its premises."""
    given = dict((binding.name, binding.value) for binding in step.params)
    worked = solved.params.get(step.id, {})
    found = []
    for declared in parameters(step.rule):
        value = given.get(declared.name)
        source = "written"
        if value is None:
            value, source = worked.get(declared.name), "derived"
        found.append({
            "name": declared.name,
            "kind": declared.kind,
            "description": declared.description,
            "required": declared.required,
            "text": "" if value is None else str(value),
            "pieces": [] if value is None else pieces(str(value)),
            "source": source if value is not None else "blank",
        })
    return found


def rest(entry) -> Dict[str, Any]:
    """One :class:`ndweb.assumptions.Rest`, ready to be set.

    The sentence is cut up like any other, so the panel sets it in the
    same face as the proof it came from and a student reads one thing
    twice rather than two things once.
    """
    text = str(entry.formula)
    return {
        "text": text,
        "pieces": pieces(text),
        "nodes": list(entry.nodes),
        "closed": list(entry.closed),
        "slots": list(entry.slots),
        "premise": entry.premise,
        "open": entry.open,
    }


def card(
    document_card,
    base_available=frozenset(),
    realisation: Optional[Realisation] = None,
    solved: Optional[Solved] = None,
) -> Dict[str, Any]:
    """One block of the sheet: where it sits, and what it says.

    ``realisation`` and ``solved`` may be passed in by a caller that has
    already worked them out -- :func:`ndweb.view.view` has, because it
    needs the proof itself to ask whether the sequent is settled.

    ``base_available`` is the sequent's premises, doing double duty: what
    may be assumed anywhere in the block, and which of the sentences it
    rests on were given rather than helped to.
    """
    root = document_card.node
    if solved is None:
        solved = solve(root, base_available)
    if realisation is None:
        realisation = realise(root, solved)
    proof = realisation.proof
    resting = rests(root, base_available, solved)
    return {
        "root": root.id,
        "x": document_card.x,
        "y": document_card.y,
        "tree": typeset(root, realisation, solved),
        "complete": realisation.complete,
        "conclusion": None if proof is None else str(proof.conclusion),
        "open": sorted(str(entry.formula) for entry in resting if entry.open),
        "assumptions": [rest(entry) for entry in resting],
        "openSlots": list(realisation.open_goals),
        "blankSlots": list(realisation.blank_goals),
    }
