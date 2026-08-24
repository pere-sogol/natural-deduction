# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## What this is

A natural deduction system for L_= (predicate logic with identity), following
Volker Halbach's *The Logic Manual* (Oxford) and its **tree-style** proof
presentation. The eventual goal is checking and building proof trees.

Roadmap, in order:

1. `nd/formula.py` — terms and formulae **(done)**
2. `nd/parser.py` — `parse("Ax(Fx -> Ey Rxy)")` **(done)**
3. `nd/proofs.py` + `nd/rules.py` — the proof tree and the 21 rules **(done)**
4. `nd/render.py` — drawing a proof as a tree **(done)**

The long-term goal is a website where proofs are built by dragging rules onto
premises, as a teaching tool. Nothing web-facing exists yet, but the deduction
layer is shaped for it — see "The deduction layer" below.

`reference/NDrules.pdf` (pp. 39–46) specifies the system precisely: the tree
definitions, every rule, and its side conditions. Consult it before changing a
rule, and note the one place we knowingly diverge from it.

## Commands

```sh
python3 -m unittest discover -s tests -t .              # whole suite (206)
python3 -m unittest tests.test_rules.TestExistential     # one class
python3 -m unittest tests.test_formula.TestCapture.test_capture_is_refused
python3 demo.py                                         # printable smoke demo
```

Run from the repo root so `import nd` resolves; a script elsewhere needs
`PYTHONPATH` pointed here.

`demo.py` lives outside the package on purpose. Running a module of `nd` as
`__main__` imports it a second time under its real name, so there are two
copies of every class — and since the dataclass `__eq__` requires an identical
class, equality silently reports False for formulae that are the same. Never
put a `__main__` block inside `nd/`.

## Environment constraints

**Python 3.9.6 (system, and the only one installed). No pytest, no venv.**
Consequences that bite:

- No `match` statements, no `dataclass(slots=True)`, no `X | Y` at runtime
  (`from __future__ import annotations` is used for annotations).
- Tests are stdlib `unittest`. Do not introduce pytest idioms.

## Architecture

`nd/formula.py` is the language; `nd/parser.py` reads it from strings;
`nd/__init__.py` re-exports both. The design is driven by what Halbach's rules
will need, not by generic AST convenience. These points are load-bearing — a
plausible-looking "cleanup" will break the deduction layer being built on top:

**There is no `⊥`.** Halbach's ¬-Intro and ¬-Elim discharge an assumption and
yield a negation directly from a contradictory pair ψ / ¬ψ. Do not add a
`Falsum` node.

**Constants are the parameters of the quantifier rules,** so every line of a
proof is a *sentence*. ∀-Intro goes from `φ(a)` to `∀v φ(v)` provided `a`
occurs neither in the conclusion nor in any undischarged assumption. Hence
`generalise()` (the inverse of substitution) and `constants()` sit alongside
`substitute()`. The system is not free-variable-based.

**`substitute()` raises `CaptureError` rather than renaming.** The textbook
proviso "t is free for v in φ" must stay reportable so an invalid ∀E can be
rejected; silently α-renaming would let a bad step succeed. `is_free_for()`
lets a caller check first.

**`__eq__` is structural, not up to α.** `Forall(x, Fx) != Forall(y, Fy)` —
correct for a proof checker, since those are distinct formulae that merely
happen to be interderivable. `alpha_equivalent()` gives the looser comparison
(de Bruijn normalisation, handles shadowing).

**∃I and =E replace *some* occurrences, not all.** From `Raa` one may infer
`∃x Rxa` as well as `∃x Rxx`. `generalise()` only produces the replace-every
reading, which is right for ∀I (the proviso guarantees full abstraction) but
wrong as a general ∃I. The rules layer must **verify** these rather than
generate them: check `φ.substitute(x, a) == premise` against the *proposed*
conclusion. No partial-replacement machinery belongs in `Formula`.

### Structural notes

- Terms are variables and constants only — L_= as the Manual presents it has
  no function symbols. `Term` is nonetheless an abstract base so a `Function`
  subclass could be added without touching the formula layer.
- One class per connective (`And`, `Or`, `Implies`, `Iff`) rather than a
  tagged `Binary(connective, l, r)`, because the rules layer dispatches on
  them constantly and 3.9 has no `match`. `_Binary` and `Quantified` hold the
  shared behaviour.
- `Equality` is separate from `Atom` so it prints infix and the identity rules
  find it without string-matching a predicate name.
- `Atom` is hand-written rather than a dataclass, because it takes varargs
  (`Atom("R", x, y)`) which `@dataclass` cannot express.
- Formulae are immutable and hashable — the rules layer will hold sets of
  undischarged assumptions.

### The parser

Notation is documented in the `nd/parser.py` module docstring. The parts that
constrain edits elsewhere:

- **`parse(str(f)) == f` is the contract.** `tests/test_parser.py` runs it over
  a corpus covering every construct. Any change to precedence, bracketing or
  spacing in `_render` must be matched in the grammar, and vice versa — the
  round-trip test is what catches drift.
- **Terms are decided by letter**: `u`–`z` are variables, `a`–`t` constants,
  both with optional `_n` subscripts. `Ab Fb` is a `ParseError`, not a
  reinterpretation.
- **Bare `A`/`E` are the quantifiers**, so they cannot be juxtaposed predicate
  letters. `nd/formula.py` therefore prints `Atom("A", x)` as `A(x)` rather
  than `Ax` — see `_QUANTIFIER_LETTERS` there, which must stay in step with the
  parser. Same for multi-letter names: `Loves(a, b)`, never `Lovesab`.
- **`Formula.parse` imports `nd.parser` inside the method body** — module-level
  would be a cycle, since the parser imports the formula classes.
- `v` is a variable letter, so a whitespace-delimited `v` is rejected with a
  hint rather than silently absorbed as a predicate argument.

**Constructors check their arguments.** `Atom`, the connectives and the
quantifiers all reject a non-`Term` / non-`Formula` argument with a `TypeError`
naming the fix, because `Atom("P", "x")` used to build happily and only fail
later inside `free_variables()`, with a traceback pointing at `nd/formula.py`
rather than at the caller. A formula must never exist in a state where its own
methods would raise. `Atom` validates *before* touching the arity registry, so
a rejected call leaves no entry behind.

### The deduction layer

`nd/proofs.py` holds the node, `nd/rules.py` the rules, `nd/render.py` the
drawing.

**A proof is a labelled tree, and `As(π)` is a set of *sentences*.** Not a set
of nodes. Discharging φ closes *every* leaf labelled φ in that subtree, so
`AndIntro(Assumption(p), Assumption(p))` rests on `{p}` and a single `→Intro`
closes both leaves. That is the book's bookkeeping, not a simplification of it.

**Every node is a sentence** — `f : S → Sent`. `Proof._seal` enforces it, so
`Assumption(parse("Fx"))` raises `SentenceError`. The quantifier rules run
through constants precisely so this stays true.

**Discharge is one uniform mechanism.** `Proof.discharged` runs parallel to
`Proof.subproofs`, each entry the frozenset of sentences that step closes in
that subproof. Every `As(π)` clause in the reference is then

```python
assumptions = union of (subproofs[i].assumptions - discharged[i])
```

computed in `_seal` and nowhere else; the renderer reads the same tuple to
place its `[φ]ⁿ` markers. Do not give a rule its own assumption arithmetic.

**Applying a rule *is* constructing the node.** `AndIntro(p, q)` is at once the
step and the proof it yields; constructors validate and raise, so an invalid
`Proof` cannot exist. `can_apply()` is `apply()` in a `try`, which is the point
— an interface that offers a rule and explains why it is unavailable must be
right about it.

**Constructor arguments follow the reference's π-numbering,** so each rule reads
off its diagram. Two look wrong and are not: `IffIntro(π₁, π₂)` takes the proof
of the *right* half first, and `OrElim(π₁, π₂, π₃)` takes the disjunction last.

**`∃Elim` enforces a proviso the reference omits.** p.45 requires `c ∉ ∃v φ` and
`c ∉ χ` for `χ ∈ As(π₂) ∖ {φ[c/v]}` — but not `c ∉ ψ`. Without the third,
`∃x Fx ⊢ Fa` goes through: take π₂ to be the bare assumption `Fa`, so
`As(π₂) ∖ {Fa}` is empty and both stated conditions hold vacuously. TLM states
the proviso with ψ included. Do not "simplify" `ExistsElim` back to the PDF.

**`∃Intro` and `=Elim` verify a proposed conclusion rather than computing one,**
because they replace *some* occurrences (see the note above). The caller passes
the target and the rule checks it. `_replaces_some()` in `nd/rules.py` does the
structural walk for `=Elim`, and belongs there rather than on `Formula`.

**The renderer is two stages.** `layout()` places sentences and bars on an
integer grid and returns data; `to_text()` paints characters into it. A web
front end reuses the first and replaces the second, so keep placement out of
the painter. Discharge numbers are assigned post-order and only to steps that
actually close a leaf, so a vacuous discharge leaves no dangling superscript.

### Three gotchas

**`repr=False` on the connective and quantifier dataclasses is deliberate.**
Without it `@dataclass` installs its own `__repr__`, clobbering the inherited
one from `_Binary` / `Quantified`.

**`EqualityElim1`/`2` inherit from `_EqualityElim` alone.** That base already
subclasses `Proof`; writing `class EqualityElim1(Proof, _EqualityElim)` is an
inconsistent MRO and fails at import.

**Predicate arities live in module-level state.** `Atom.__init__` fixes a
letter's arity on first use and raises `ArityError` on a later mismatch, so
writing `Rx` where `Rxy` was meant is caught. Every test case must call
`reset_arities()` in `setUp` or arities leak between cases.

## Conventions

- **British spelling** in identifiers and prose (`generalise`).
- `→` is `.implies()`, not `>>`: Python binds `>>` more tightly than `&` and
  `|`, so `p & q >> r` would quietly parse as `p & (q >> r)`. `~`, `&` and `|`
  are overloaded and safe.
- Printing follows the book: minimal brackets, `¬` > `∧` > `∨` > `→`/`↔`
  (right-associative), quantifiers taking smallest scope (`∀x Fx → Ga` means
  `(∀x Fx) → Ga`), and a space after the bound variable only before a
  predicate letter — `∀x Fx`, but `∀x(Fx → Gx)`, `∀x∃y Rxy`, `∀x¬Fx`.
  `→` and `↔` share a precedence level, so one nested directly in the other is
  *always* bracketed: `P → (Q ↔ S)`. The parser rejects the unbracketed form.
- Docstrings use ASCII for logical symbols (`Ax`, `Ey`, `->`) to avoid
  encoding noise in source; `__str__` output and tests use Unicode.
