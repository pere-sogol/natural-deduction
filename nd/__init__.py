"""Natural deduction for L_= , following Halbach's *The Logic Manual*.

The language is in :mod:`nd.formula`, with a reader for the book's
notation in :mod:`nd.parser`.  On top of those sit the deduction layer --
:mod:`nd.proofs` for the proof tree and :mod:`nd.rules` for the rules
themselves -- and :mod:`nd.render`, which draws a proof the way the book
does.

    >>> from nd import *
    >>> print(ImpliesIntro(Assumption(parse("P")), parse("P")))
     [P]¹
    ───── →I, 1
    P → P
"""

from nd.formula import (
    And,
    ArityError,
    Atom,
    CaptureError,
    Constant,
    Equality,
    Exists,
    Forall,
    Formula,
    FormulaError,
    Iff,
    Implies,
    Not,
    Or,
    Quantified,
    Term,
    Variable,
    declared_arities,
    fresh_constant,
    fresh_variable,
    reset_arities,
)
from nd.parser import ParseError, parse, parse_term
from nd.proofs import (
    MismatchError,
    Parameter,
    Proof,
    ProofError,
    ProvisoError,
    RuleError,
    SentenceError,
    ShapeError,
    apply,
    can_apply,
    rule,
    rule_catalogue,
)
from nd.render import Layout, PlacedBar, PlacedFormula, layout, to_text
from nd.rules import (
    AndElim1,
    AndElim2,
    AndIntro,
    Assumption,
    EqualityElim1,
    EqualityElim2,
    EqualityIntro,
    ExistsElim,
    ExistsIntro,
    ForallElim,
    ForallIntro,
    IffElim1,
    IffElim2,
    IffIntro,
    ImpliesElim,
    ImpliesIntro,
    NotElim,
    NotIntro,
    OrElim,
    OrIntro1,
    OrIntro2,
)

__all__ = [
    "FormulaError",
    "ArityError",
    "CaptureError",
    "Term",
    "Variable",
    "Constant",
    "Formula",
    "Atom",
    "Equality",
    "Not",
    "And",
    "Or",
    "Implies",
    "Iff",
    "Quantified",
    "Forall",
    "Exists",
    "fresh_variable",
    "fresh_constant",
    "reset_arities",
    "declared_arities",
    "ParseError",
    "parse",
    "parse_term",
    # the deduction layer
    "ProofError",
    "SentenceError",
    "RuleError",
    "ShapeError",
    "MismatchError",
    "ProvisoError",
    "Parameter",
    "Proof",
    "rule",
    "rule_catalogue",
    "apply",
    "can_apply",
    "Assumption",
    "EqualityIntro",
    "AndIntro",
    "AndElim1",
    "AndElim2",
    "OrIntro1",
    "OrIntro2",
    "OrElim",
    "ImpliesIntro",
    "ImpliesElim",
    "NotIntro",
    "NotElim",
    "IffIntro",
    "IffElim1",
    "IffElim2",
    "ForallIntro",
    "ForallElim",
    "ExistsIntro",
    "ExistsElim",
    "EqualityElim1",
    "EqualityElim2",
    # drawing
    "Layout",
    "PlacedFormula",
    "PlacedBar",
    "layout",
    "to_text",
]
