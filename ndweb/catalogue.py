"""What the palette shows: every rule, described for a student.

The catalogue is read off :func:`nd.proofs.rule_catalogue`, so a rule
added to the engine appears here without being registered twice.  Only
the prose is written here rather than taken from the rule's docstring:
those docstrings address whoever maintains the checker and are written in
ASCII (``phi``, ``->``, ``^``) for the sake of the source, which reads
badly in a tooltip.  ``SUMMARIES`` is the student-facing wording, and a
test asserts it covers the catalogue exactly, so a new rule cannot slip
in without one.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Dict, Optional, Tuple

from nd.proofs import rule, rule_catalogue

__all__ = [
    "RuleInfo", "ParameterInfo", "catalogue", "describe", "SUMMARIES", "SCHEMA",
]

#: One line per rule, in the book's symbols.  Keyed by ``cls.name``.
SUMMARIES = {
    "Assumption": "Assume a sentence. It stays open until some rule discharges it.",
    "=Intro": "Any constant is identical to itself: write c = c, resting on nothing.",
    "∧Intro": "From φ and ψ, conclude φ ∧ ψ.",
    "∧Elim1": "From φ ∧ ψ, conclude φ.",
    "∧Elim2": "From φ ∧ ψ, conclude ψ.",
    "∨Intro1": "From φ, conclude φ ∨ ψ for any ψ you choose.",
    "∨Intro2": "From ψ, conclude φ ∨ ψ for any φ you choose.",
    "∨Elim": "Proof by cases: if φ ∨ ψ, and χ follows from each, conclude χ.",
    "→Intro": "Prove φ while assuming ψ, then conclude ψ → φ and discharge ψ.",
    "→Elim": "From ψ and ψ → φ, conclude φ.",
    "¬Intro": "Assume φ and reach a contradiction, then conclude ¬φ.",
    "¬Elim": "Assume ¬φ and reach a contradiction, then conclude φ.",
    "↔Intro": "Prove each half from the other, then conclude φ ↔ ψ.",
    "↔Elim1": "From φ ↔ ψ and φ, conclude ψ.",
    "↔Elim2": "From φ ↔ ψ and ψ, conclude φ.",
    "∀Intro": "From φ proved of an arbitrary c, conclude ∀v φ.",
    "∀Elim": "From ∀v φ, conclude φ with any constant put for v.",
    "∃Intro": "From φ with c in it, conclude ∃v φ.",
    "∃Elim": "From ∃v φ, and χ proved from a fresh instance of φ, conclude χ.",
    "=Elim1": "From c₁ = c₂ and a sentence, replace occurrences of c₁ by c₂.",
    "=Elim2": "From c₁ = c₂ and a sentence, replace occurrences of c₂ by c₁.",
}

#: Each rule's own figure: the premises above the bar, what it concludes,
#: and what it discharges from each premise.
#:
#: The premises are in the order the constructor takes them, which is the
#: reference's numbering, so the two that look wrong are meant to: ``↔Intro``
#: proves the right half first, and ``∨Elim`` takes its disjunction last.
#: A student reading the figure is reading the argument order as well.
SCHEMA = {
    "Assumption": ((), "φ", ()),
    "=Intro": ((), "c = c", ()),
    "∧Intro": (("φ", "ψ"), "φ ∧ ψ", ()),
    "∧Elim1": (("φ ∧ ψ",), "φ", ()),
    "∧Elim2": (("φ ∧ ψ",), "ψ", ()),
    "∨Intro1": (("φ",), "φ ∨ ψ", ()),
    "∨Intro2": (("ψ",), "φ ∨ ψ", ()),
    "∨Elim": (("χ", "χ", "φ ∨ ψ"), "χ", ("φ", "ψ", None)),
    "→Intro": (("ψ",), "φ → ψ", ("φ",)),
    "→Elim": (("φ", "φ → ψ"), "ψ", ()),
    "¬Intro": (("ψ", "¬ψ"), "¬φ", ("φ", "φ")),
    "¬Elim": (("ψ", "¬ψ"), "φ", ("¬φ", "¬φ")),
    "↔Intro": (("ψ", "φ"), "φ ↔ ψ", ("φ", "ψ")),
    "↔Elim1": (("φ ↔ ψ", "φ"), "ψ", ()),
    "↔Elim2": (("φ ↔ ψ", "ψ"), "φ", ()),
    "∀Intro": (("φ(c)",), "∀v φ(v)", ()),
    "∀Elim": (("∀v φ(v)",), "φ(c)", ()),
    "∃Intro": (("φ(c)",), "∃v φ(v)", ()),
    "∃Elim": (("∃v φ(v)", "χ"), "χ", (None, "φ(c)")),
    "=Elim1": (("c = d", "φ(c)"), "φ(d)", ()),
    "=Elim2": (("c = d", "φ(d)"), "φ(c)", ()),
}

#: The provisos worth warning about before a student runs into them.
CAVEATS = {
    "∀Intro": "c must be arbitrary: absent from every assumption still open.",
    "∃Elim": "c must be fresh: absent from the existential, from the conclusion, "
             "and from every other assumption still open.",
    "∃Intro": "Replaces some occurrences, not necessarily all: Raa gives ∃x Rxa "
              "as well as ∃x Rxx.",
    "=Elim1": "Replaces some occurrences, not necessarily all.",
    "=Elim2": "Replaces some occurrences, not necessarily all.",
}

_CONNECTIVES = ("∧", "∨", "→", "↔", "¬", "∀", "∃", "=")


@dataclass(frozen=True)
class ParameterInfo:
    """A value the rule needs besides its subproofs."""

    name: str
    kind: str  # "formula", "constant" or "variable"
    description: str
    required: bool


@dataclass(frozen=True)
class RuleInfo:
    """Everything the palette needs about one rule."""

    name: str
    label: str
    subproofs: int
    parameters: Tuple[ParameterInfo, ...]
    summary: str
    caveat: str
    group: str       # "leaf", "intro" or "elim"
    connective: str  # "" for Assumption


def _group(name: str, subproof_count: int) -> str:
    if subproof_count == 0:
        return "leaf"
    return "intro" if "Intro" in name else "elim"


def _connective(name: str) -> str:
    for symbol in _CONNECTIVES:
        if name.startswith(symbol):
            return symbol
    return ""


def describe(name: str) -> RuleInfo:
    """The palette entry for one rule, by either of its names."""
    cls = rule(name)
    return RuleInfo(
        name=cls.name,
        label=cls.label,
        subproofs=cls.subproof_count,
        parameters=tuple(
            ParameterInfo(p.name, p.kind, p.description, p.required)
            for p in cls.parameters
        ),
        summary=SUMMARIES.get(cls.name, ""),
        caveat=CAVEATS.get(cls.name, ""),
        group=_group(cls.name, cls.subproof_count),
        connective=_connective(cls.name),
    )


def catalogue() -> Tuple[RuleInfo, ...]:
    """Every rule, in the order the reference introduces them."""
    return tuple(describe(cls.name) for cls in rule_catalogue())
