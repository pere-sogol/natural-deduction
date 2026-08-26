# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## What this is

A natural deduction system for L_= (predicate logic with identity), following
Volker Halbach's *The Logic Manual* (Oxford) and its **tree-style** proof
presentation. The eventual goal is checking and building proof trees.

Roadmap, in order:

1. `nd/formula.py` — terms and formulae **(done)**
2. `nd/parser.py` — `parse("Ax(Fx -> Ey Rxy)")` **(done)**
3. `nd/proofs.py` + `nd/rules.py` — the proof tree and the 17 rules **(done)**
4. `nd/render.py` — drawing a proof as a tree **(done)**
5. `ndweb/` + `web/` — the browser sandbox **(done)**

The editor runs entirely in the browser: Pyodide loads this very package into
WebAssembly, so the checker a student uses is the checker these tests cover.
Proofs are typeset by the browser rather than placed on a character grid.
See "The editor layer" below.

`reference/NDrules.pdf` (pp. 39–46) specifies the system precisely: the tree
definitions, every rule, and its side conditions. Consult it before changing a
rule, and note the two kinds of place we knowingly diverge from it: the
`∃Elim` proviso, and the four numbered pairs that are single rules here.

## Commands

```sh
python3 -m unittest discover -s tests -t .              # whole suite (405)
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

**Four numbered pairs are single rules here.** The reference states (∧Elim1)/
(∧Elim2), (∨Intro1)/(∨Intro2), (↔Elim1)/(↔Elim2) and (=Elim1)/(=Elim2)
separately, but nothing a proof records distinguishes the halves of any pair:
the same premises, the same node, the same label on the bar. Splitting them only
forced the caller to pick a side before it had a formula in hand.

`AndElim(π₁, conclusion)`, `OrIntro(π₁, conclusion)` and
`EqualityElim(π₁, π₂, conclusion)` join the verify-don't-compute family above —
a conjunction has two conjuncts, a disjunction may add anything at all, an
identity reads both ways, and none of it is guessable — so the sentence wanted
is named and checked. `IffElim(π₁, π₂)` needs no parameter at all: the half
supplied by π₂ decides the direction, which is why merging it costs nothing.

Two traps. `∧Elim` takes a conjunct *whole* and never reaches inside one: from
`(P ∧ Q) ∧ S` it gives `P ∧ Q` or `S`, never `P`. And `↔Elim` can no longer
appear in `unify.MAJOR` — `φ ↔ ψ` alone does not say which half it is about to
be handed. `tests/test_rules.py` pins the first; the comment on `MAJOR` records
the second.

**The renderer is two stages.** `layout()` places sentences and bars on an
integer grid and returns data; `to_text()` paints characters into it. A web
front end reuses the first and replaces the second, so keep placement out of
the painter. Discharge numbers are assigned post-order and only to steps that
actually close a leaf, so a vacuous discharge leaves no dangling superscript.

### Two gotchas

**`repr=False` on the connective and quantifier dataclasses is deliberate.**
Without it `@dataclass` installs its own `__repr__`, clobbering the inherited
one from `_Binary` / `Quantified`.

**Predicate arities live in module-level state.** `Atom.__init__` fixes a
letter's arity on first use and raises `ArityError` on a later mismatch, so
writing `Rx` where `Rxy` was meant is caught. Every test case must call
`reset_arities()` in `setUp` or arities leak between cases.

## The editor layer

`ndweb/` is the editor's own model and `web/` the page that draws it. `ndweb`
imports `nd`; nothing goes the other way, and `nd` is unchanged by any of it.

The editor is a **sandbox**, and that word is doing work. A rule can be put
down anywhere, with nothing decided about it, and filled in afterwards in
whatever order suits. There is no dialogue asking what a rule will need before
it may be used, no privileged tree, and nothing is refused for being premature.
What used to be asked in advance — which sentence, which parameter, which of two
premises — is a **slot on the block**, and `ndweb/unify.py` fills in whichever
of them the others settle.

**A `Derivation` is not a `Proof`, and must not become one.** A proof is
complete and valid by construction; a proof being *built* has holes, and a hole
proves nothing. So `ndweb.derivation` owns a tree of `Goal` (a slot) and `Step`
(a rule applied to children that may be slots), and `realise()` projects a
hole-free derivation onto a real `Proof` by calling `apply()`. Keeping the two
apart is what lets `nd` go on promising that holding a `Proof` means holding a
proof.

**Every `Proof` in the application is made by `apply()`.** `ndweb` never
constructs one directly, which is what allows `ndweb/refine.py` and
`ndweb/unify.py` to guess. A wrong entry there can send a student down a branch
that leads nowhere; it cannot make the editor accept a bad proof.
`tests/test_purity.py` enforces this by asserting that no name from
`nd.rules.__all__` is reachable from any `ndweb` module — a comment would not
have survived.

**`Goal.target` is optional.** A workspace where every hole had to announce what
it would eventually contain could only be driven backwards from a goal. Blank
slots are what make the board a board.

**The document is a flat forest of `Card`s, each with an `(x, y)`.** There is no
`main` tree and no bench. A block becomes the answer by *proving* the sequent,
which `view` checks over every card, rather than by sitting in a special place.
Position is the student's arrangement and nothing in the logic reads it — but it
is kept in the document all the same, because a board whose pieces jump about
whenever anything is checked is not a board anybody can think on.

**Forward inference is the engine, not a second table.** `unify.predict` stands
each premise sentence up as an `Assumption` and applies the real rule. A premise
slot holding `φ` with nothing above it *is* an assumption of `φ`, so this is not
a simulation — it is the rule, on the proof as it currently stands. There is
therefore no `predict()` table to drift from `nd/rules.py`.

**Two rules are exempted from that, and only while unfinished.** `∀Intro` and
`∃Elim` carry provisos about a parameter being arbitrary or fresh, and those are
conditions on the whole subtree. While the branches above are holes the proviso
is *unsettled*, not broken, so `unify._UNSETTLED` predicts the conclusion the
rule would reach. Nothing is proved by it: `realise` applies the same rule to
the real subproofs and lets the proviso bite. Do not widen that dict.

**`unify.FROM_PREMISE` is where a backward question is answered by a slot.**
`refine` asks `→Elim` for an antecedent; on the sheet that antecedent is the
left premise, so if it has been written there is nothing to ask. Three lines of
table replaced the whole modal-dialogue flow.

**`unify.MAJOR` is the other half of that.** An elimination given only its major
premise already knows what it concludes and what its other premises must be, and
saying so is most of what makes the sheet feel as though it is helping. Only
`→Elim` qualifies now: an elimination that reads its direction off a *minor*
premise — `↔Elim` does — cannot be in the table, because the major premise alone
leaves the answer open.

**Solved parameters are computed, never stored** — as contexts are, and for the
same reason. A `→Intro` whose conclusion was written knows perfectly well what
it discharges; writing that into the document would only let the two disagree.
`realise(node, solved)` takes them; `discharges(step, resolve, values)` takes
them; nothing persists them.

**`CONCLUSION_PARAM` stops one value being typed twice.** `∃Intro` is told the
existential it claims, `¬Elim` the sentence it concludes, `=Elim` the rewritten
sentence, `∧Elim` which conjunct it takes, `∨Intro` the disjunction it claims,
`Assumption` what is assumed — and in every case that value is also the line
under the bar. `kwargs()` fills the parameter from `claim`, and `parameters()`
hides it from the block. That is what lets `∧Elim` and `∨Intro` be single rules
without adding a chip: on the sheet you say which conjunct, or which
disjunction, by writing it — which you would have written anyway.

**Contexts are computed, never stored.** What may be assumed at a slot depends
on every discharging step above it, so a field on `Goal` would go stale the
moment any of them changed. `unify.solve` walks down from the premises instead.
It is advisory: a slot may be closed by something resting on other assumptions,
and the proof still stands with that assumption left open. Telling a student
"you proved it, but not from what you were given" beats refusing the step.

**`discharge.py` duplicates what `Proof.discharged` records,** because the
editor needs it before the step exists. `tests/test_discharge.py` checks the two
agree for every realisable step in the corpus, which is what keeps the copy
honest — the same trick `parse(str(f)) == f` plays for the printer and the
parser.

**∀Intro backwards needs a parameter fresh in the *goal*, not merely arbitrary.**
`generalise()` abstracts every occurrence, so refining `∀x Rxa` at `c = a` gives
the subgoal `Raa`, which generalises to `∀x Rxx` — a branch that can never reach
the target. `refine` refuses that outright, which is stricter than the engine and
the safe direction. Arbitrariness proper can only be *warned* about, since the
offending assumption may yet be discharged.

**Joining two blocks is not checked.** Dropping a block into a slot it does not
fit is allowed, and the bar then says what it actually proves. Refusing would
leave the student holding a block with nowhere to put it and no explanation;
`Step.claim` turns it into a located *drift* error instead.

### Setting, not drawing

**`nd/render.py` is no longer what the page uses, and still earns its keep.**
`layout()` places sentences on an integer grid, which is right for a terminal
and wrong for a page: it assumes one glyph is one cell, so the figure hangs on
the reader having a monospace font containing `∀ ∃ → ↔`, and it fixes every
width in Python, so a proof cannot reflow. `ndweb/typeset.py` emits the
**nesting** instead — premises in a row, a bar, a conclusion — and the browser
measures the type, the way `bussproofs` lets TeX do it.

What `layout()` is still called for is the **discharge numbering**, which is
genuinely subtle: numbers rise as the eye travels down, a step closing nothing
gets none, and one number can mark several leaves. `typeset` runs the layout,
throws the placement away and keeps the annotation, zipping it post-order.
`tests/test_render.py` pins that correspondence. Do not reimplement the
numbering.

**`shadow.py` is still what makes that possible.** `layout()` reads six members
off a node and never asks whether it has a `Proof`, so a derivation with holes
draws through the book's own renderer. A slot is given an empty assumption set
so that no step below brackets it as discharged — it rests on nothing yet, and
the bracket would then vanish once it was filled.

**`typeset.pieces()` is a lossless lexer over the *printed* sentence.** It
classifies each character — predicate, variable, constant, connective, subscript
— so CSS can set the letters italic and put proper space around the connectives.
Reading the printed string rather than the formula sounds backwards and is not:
it guarantees that what is set is exactly what `Formula.__str__` produced, which
is the string the parser reads back. Nothing is dropped: a space a connective
supplies itself is *marked* `tight` rather than removed, and a subscript's
underscore is a piece of its own, so `"".join(p["t"] for p in pieces(s)) == s`.
`tests/test_typeset.py` pins that, and pins `parse(joined) == f` on top of it.

**The Python/JS boundary is one function, JSON string in and JSON string out.**
Passing objects would be faster and would cost the thing that matters: the tests
drive the literal call the browser drives, and `json.dumps` fails loudly if a
`Formula` ever escapes into the view. There is no browser automation on this
machine, so anything that can only be tested in a browser is effectively
untested — hence the rule at the top of `web/render.js`: **if a JS function would
want a unit test, it belongs in Python.**

**No `__main__` inside `ndweb/` either,** for the reason given above for `nd/`.
`web/bootstrap.py` and `web/serve.py` are the entry points, outside both
packages as `demo.py` is.

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
