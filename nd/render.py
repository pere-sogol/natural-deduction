"""Drawing a proof as a tree, in the style of the book.

Two stages.  :func:`layout` places every sentence and every inference bar
on an integer grid and returns the result as data; :func:`to_text` paints
that grid with characters.  The split is deliberate: the placement is the
part worth keeping when the drawing moves to a browser, where the painter
becomes elements rather than characters.

Conclusions sit at the bottom, assumptions at the top, each inference bar
spanning the premises above it with its rule written to the right.  A
discharged assumption is bracketed and given the number of the step that
discharged it::

    [P]¹    P → Q
    ───────────── →E
          Q
    ───────────── →I, 1
        P → Q

Numbering runs bottom-up through the tree, so the numbers grow as the eye
travels down the page.  Only steps that actually close a leaf are
numbered; a rule may discharge an assumption that was never made, and
labelling that would leave a number pointing at nothing.

Where the same sentence labels two leaves, one discharge closes both --
``As(pi)`` is a set of sentences -- and both get the same number.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Dict, List, Optional, Tuple

from nd.formula import Formula
from nd.proofs import Proof

__all__ = ["PlacedFormula", "PlacedBar", "Layout", "layout", "to_text"]

#: Blank columns between sibling subproofs.
GUTTER = 3

_SUPERSCRIPTS = {
    "0": "⁰", "1": "¹", "2": "²", "3": "³", "4": "⁴",
    "5": "⁵", "6": "⁶", "7": "⁷", "8": "⁸", "9": "⁹",
}


def _superscript(number: int, ascii_only: bool) -> str:
    digits = str(number)
    if ascii_only:
        return digits
    return "".join(_SUPERSCRIPTS[d] for d in digits)


# --------------------------------------------------------------------------
# What a layout consists of
# --------------------------------------------------------------------------


@dataclass(frozen=True)
class PlacedFormula:
    """One sentence, placed. ``y`` counts rows down from the top."""

    x: int
    y: int
    text: str
    formula: Formula
    #: The number of the step discharging this leaf, if it is discharged.
    discharge: Optional[int] = None
    #: A leaf rule's label, written to the right; only ``=Intro`` has one.
    note: str = ""


@dataclass(frozen=True)
class PlacedBar:
    """One inference bar, with its rule written just past the right end."""

    x: int
    y: int
    width: int
    label: str


@dataclass(frozen=True)
class Layout:
    """A whole proof, placed on a grid ``width`` by ``height``."""

    width: int
    height: int
    formulae: Tuple[PlacedFormula, ...]
    bars: Tuple[PlacedBar, ...]


# --------------------------------------------------------------------------
# Working out which steps discharge which leaves
# --------------------------------------------------------------------------


class _Annotation:
    """Mirrors the proof tree, recording discharge before numbers exist.

    Numbers cannot be handed out on the way down, because a step earns one
    only if some leaf below it is actually closed by that step -- and an
    inner step discharging the same sentence gets there first.  So the
    descent marks steps and leaves with anonymous tokens, and a second
    pass turns the tokens that were used into consecutive numbers.
    """

    __slots__ = ("token", "marker", "children")

    def __init__(self, token, marker, children) -> None:
        self.token = token
        self.marker = marker
        self.children = children


def _annotate(proof: Proof, closing: Dict[Formula, object]) -> _Annotation:
    if proof.is_leaf:
        # Only a leaf that is an assumption can be discharged.  An
        # ``=Intro`` node rests on nothing, so a step discharging c=c
        # elsewhere must not bracket it as though it had closed this.
        marker = None
        if proof.conclusion in proof.assumptions:
            marker = closing.get(proof.conclusion)
        return _Annotation(None, marker, ())
    token = object() if any(proof.discharged) else None
    children = []
    for subproof, group in zip(proof.subproofs, proof.discharged):
        inner = closing
        if group:
            inner = dict(closing)
            for formula in group:
                # Written unconditionally, so the innermost step to
                # discharge a sentence is the one that owns the leaf.
                inner[formula] = token
        children.append(_annotate(subproof, inner))
    return _Annotation(token, None, tuple(children))


def _collect_used(annotation: _Annotation, used: set) -> None:
    if annotation.marker is not None:
        used.add(annotation.marker)
    for child in annotation.children:
        _collect_used(child, used)


def _assign(
    annotation: _Annotation, used: set, counter: List[int], numbers: Dict[object, int]
) -> None:
    # Post-order, so a step is numbered after everything above it and the
    # numbers increase down the page.
    for child in annotation.children:
        _assign(child, used, counter, numbers)
    if annotation.token is not None and annotation.token in used:
        counter[0] += 1
        numbers[annotation.token] = counter[0]


# --------------------------------------------------------------------------
# Placement
# --------------------------------------------------------------------------


@dataclass
class _Block:
    """A laid-out subtree, in coordinates local to itself.

    ``conclusion_x`` and ``conclusion_width`` locate the bottom line, which
    is what the parent's bar has to span.
    """

    width: int
    height: int
    conclusion_x: int
    conclusion_width: int
    formulae: List[PlacedFormula] = field(default_factory=list)
    bars: List[PlacedBar] = field(default_factory=list)

    def shift(self, dx: int, dy: int) -> None:
        if dx == 0 and dy == 0:
            return
        self.formulae = [
            PlacedFormula(f.x + dx, f.y + dy, f.text, f.formula, f.discharge, f.note)
            for f in self.formulae
        ]
        self.bars = [PlacedBar(b.x + dx, b.y + dy, b.width, b.label) for b in self.bars]
        self.conclusion_x += dx


def _build(
    proof: Proof,
    annotation: _Annotation,
    numbers: Dict[object, int],
    ascii_only: bool,
) -> _Block:
    if proof.is_leaf:
        return _leaf_block(proof, annotation, numbers, ascii_only)

    blocks = [
        _build(subproof, child, numbers, ascii_only)
        for subproof, child in zip(proof.subproofs, annotation.children)
    ]

    # Siblings stand side by side, bottom-aligned so their conclusions --
    # the premises of this step -- share a row.
    premise_row = max(block.height for block in blocks)
    offset = 0
    for block in blocks:
        block.shift(offset, premise_row - block.height)
        offset += block.width + GUTTER
    children_width = offset - GUTTER

    span_start = blocks[0].conclusion_x
    span_end = blocks[-1].conclusion_x + blocks[-1].conclusion_width

    text = str(proof.conclusion)
    # The bar spans the premises, but never less than the line beneath it.
    bar_width = max(span_end - span_start, len(text))
    bar_x = (span_start + span_end - bar_width) // 2
    conclusion_x = bar_x + (bar_width - len(text)) // 2

    label = proof.label
    number = numbers.get(annotation.token)
    if number is not None:
        label = "{0}, {1}".format(label, number)

    block = _Block(0, premise_row + 2, conclusion_x, len(text))
    for child in blocks:
        block.formulae.extend(child.formulae)
        block.bars.extend(child.bars)
    block.bars.append(PlacedBar(bar_x, premise_row, bar_width, label))
    block.formulae.append(
        PlacedFormula(conclusion_x, premise_row + 1, text, proof.conclusion)
    )

    # A wide conclusion can push the bar left of everything above it.
    block.shift(max(0, -bar_x), 0)
    bar = block.bars[-1]
    block.width = max(
        children_width + max(0, -bar_x),
        bar.x + bar.width + (1 + len(label) if label else 0),
        block.conclusion_x + len(text),
    )
    return block


def _leaf_block(
    proof: Proof,
    annotation: _Annotation,
    numbers: Dict[object, int],
    ascii_only: bool,
) -> _Block:
    text = str(proof.conclusion)
    number = numbers.get(annotation.marker)
    if number is not None:
        text = "[{0}]{1}".format(text, _superscript(number, ascii_only))
    note = proof.label  # "=I"; an assumption has none
    width = len(text) + (2 + len(note) if note else 0)
    block = _Block(width, 1, 0, len(text))
    block.formulae.append(
        PlacedFormula(0, 0, text, proof.conclusion, number, note)
    )
    return block


# --------------------------------------------------------------------------
# The public entry points
# --------------------------------------------------------------------------


def layout(proof: Proof, ascii_only: bool = False) -> Layout:
    """Place every sentence and bar of ``proof`` on a grid.

    ``ascii_only`` affects the discharge markers, and so the widths: plain
    digits rather than superscripts.
    """
    annotation = _annotate(proof, {})
    used: set = set()
    _collect_used(annotation, used)
    numbers: Dict[object, int] = {}
    _assign(annotation, used, [0], numbers)
    block = _build(proof, annotation, numbers, ascii_only)
    return Layout(
        block.width, block.height, tuple(block.formulae), tuple(block.bars)
    )


def to_text(proof: Proof, ascii_only: bool = False) -> str:
    """Draw ``proof`` as text.

    With ``ascii_only`` the bars are drawn with hyphens and the discharge
    numbers are plain digits, for terminals that mangle the rest.  The
    sentences themselves are always the book's symbols.
    """
    placed = layout(proof, ascii_only)
    rule_character = "-" if ascii_only else "─"
    grid = [[" "] * placed.width for _ in range(placed.height)]

    def paint(x: int, y: int, text: str) -> None:
        for index, character in enumerate(text):
            grid[y][x + index] = character

    for bar in placed.bars:
        paint(bar.x, bar.y, rule_character * bar.width)
        if bar.label:
            paint(bar.x + bar.width + 1, bar.y, bar.label)
    for formula in placed.formulae:
        paint(formula.x, formula.y, formula.text)
        if formula.note:
            paint(formula.x + len(formula.text) + 2, formula.y, formula.note)

    return "\n".join("".join(row).rstrip() for row in grid)
