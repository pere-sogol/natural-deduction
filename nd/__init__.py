"""Natural deduction for L_= , following Halbach's *The Logic Manual*.

At present this package provides the language only: terms, formulae, and
the operations the deduction rules will be built on.  See
:mod:`nd.formula`.
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
]
