"""Documents to JSON and back.

The wire format is a snapshot rather than a journal of edits.  Because
every node is immutable, a snapshot costs nothing to take and an undo
stack is a list of them; and because a snapshot is a flat list of nodes in
dependency order, it can equally be replayed one node at a time to show a
proof being assembled.  One format serves saving, sharing and stepping
through.

There is no per-rule knowledge here.  A parameter's kind is read off
``rule(name).parameters``, and the value decoded with ``parse`` or
``parse_term`` accordingly -- so a rule added to the engine serialises
without this module being touched.  That is the catalogue design paying
for itself.
"""

from __future__ import annotations

import base64
import json
import zlib
from typing import Any, Dict, List, Optional

from nd.formula import Constant, Formula, Variable, reset_arities
from nd.parser import parse, parse_term
from nd.proofs import rule

from ndweb.derivation import Binding, Card, Document, Goal, Node, Step

__all__ = ["encode", "decode", "to_json", "from_json", "to_fragment", "from_fragment"]

_VERSION = 2


def _kinds(rule_name: str) -> Dict[str, str]:
    try:
        return dict((p.name, p.kind) for p in rule(rule_name).parameters)
    except KeyError:
        return {}


def _encode_node(node: Node) -> Dict[str, Any]:
    if isinstance(node, Goal):
        return {
            "id": node.id,
            "kind": "goal",
            "target": None if node.target is None else str(node.target),
        }
    return {
        "id": node.id,
        "kind": "step",
        "rule": node.rule,
        "children": [_encode_node(child) for child in node.children],
        "params": dict((b.name, str(b.value)) for b in node.params),
        "claim": None if node.claim is None else str(node.claim),
    }


def _decode_node(raw: Dict[str, Any]) -> Node:
    if raw.get("kind") == "goal":
        target = raw.get("target")
        return Goal(int(raw["id"]), parse(target) if target else None)
    rule_name = raw["rule"]
    kinds = _kinds(rule_name)
    params = []
    for name, text in sorted((raw.get("params") or {}).items()):
        kind = kinds.get(name, "formula")
        if kind == "formula":
            value = parse(text)
        else:
            term = parse_term(text)
            value = term if kind != "variable" or isinstance(term, Variable) else term
        params.append(Binding(name, value))
    claim = raw.get("claim")
    return Step(
        int(raw["id"]),
        rule_name,
        tuple(_decode_node(child) for child in raw.get("children") or ()),
        tuple(params),
        parse(claim) if claim else None,
    )


def encode(document: Document) -> Dict[str, Any]:
    """A document as plain JSON-able data."""
    return {
        "version": _VERSION,
        "goal": None if document.goal is None else str(document.goal),
        "premises": [str(premise) for premise in document.premises],
        "cards": [
            {"x": card.x, "y": card.y, "node": _encode_node(card.node)}
            for card in document.cards
        ],
        "nextId": document.next_id,
    }


def decode(raw: Dict[str, Any]) -> Document:
    """Read a document back.

    Arities are forgotten first: a document is self-contained, and the
    predicate letters it uses must not have to agree with whatever was
    being edited a moment ago.
    """
    reset_arities()
    goal = raw.get("goal")
    return Document(
        goal=parse(goal) if goal else None,
        premises=tuple(parse(text) for text in raw.get("premises") or ()),
        cards=tuple(
            Card(
                _decode_node(entry["node"]),
                int(entry.get("x") or 0),
                int(entry.get("y") or 0),
            )
            for entry in raw.get("cards") or ()
        ),
        next_id=int(raw.get("nextId") or 0),
    )


def to_json(document: Document) -> str:
    return json.dumps(encode(document), ensure_ascii=False, sort_keys=True)


def from_json(text: str) -> Document:
    return decode(json.loads(text))


def to_fragment(document: Document) -> str:
    """A document squeezed into something that will sit in a URL."""
    packed = zlib.compress(to_json(document).encode("utf-8"), 9)
    return base64.urlsafe_b64encode(packed).decode("ascii").rstrip("=")


def from_fragment(fragment: str) -> Document:
    padding = "=" * (-len(fragment) % 4)
    packed = base64.urlsafe_b64decode(fragment + padding)
    return from_json(zlib.decompress(packed).decode("utf-8"))
