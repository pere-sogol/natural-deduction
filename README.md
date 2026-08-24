# naturaldeduction

A natural deduction system for **L₌** — predicate logic with identity — following
Volker Halbach's *The Logic Manual* (Oxford) and its **tree-style** presentation
of proofs.

You write formulae, apply the rules, and get back a proof tree that has been
checked as you built it: the provisos on the quantifier rules are enforced at the
moment you apply them, and a proof that violates one is refused with a message
saying which. Proofs draw themselves the way the book does.

```python
>>> from nd import *
>>> denial = Assumption(parse("Ax ~Fx"))
>>> contradiction = NotIntro(
...     Assumption(parse("Fa")), ForallElim(denial, Constant("a")), parse("Ax ~Fx")
... )
>>> print(ExistsElim(Assumption(parse("Ex Fx")), contradiction, Constant("a")))
                [∀x¬Fx]¹
                ──────── ∀E
        [Fa]²     ¬Fa
        ───────────── ¬I, 1
∃x Fx      ¬∀x¬Fx
───────────────── ∃E, 2
     ¬∀x¬Fx
```

## Status

The language, the parser, all 21 rules and the renderer are written and tested.
There is no proof *search* and no web interface; the longer-term aim is a site
where proofs are built by dragging rules onto premises, and the API is shaped
with that in mind, but none of it exists yet.

## Requirements

Python 3.9 or later. No dependencies, no build step — the standard library is
all it uses, and the tests are `unittest`.

Run things from the repository root so that `import nd` resolves.

## Formulae

Three ways to build the same thing:

```python
from nd import *

x, y = Variable("x"), Variable("y")
a = Constant("a")

claim = Forall(x, Implies(Atom("F", x), Exists(y, Atom("R", x, y))))
claim = Forall(x, Atom("F", x).implies(Exists(y, Atom("R", x, y))))
claim = parse("Ax(Fx -> Ey Rxy)")

print(claim)                  # ∀x(Fx → ∃y Rxy)
claim.is_sentence()           # True
claim.free_variables()        # frozenset()
```

`~`, `&` and `|` are overloaded. `→` is `.implies()` and `↔` is `.iff()`, spelled
out rather than given to an operator because Python binds `>>` more tightly than
`&`, so `p & q >> r` would quietly mean `p & (q >> r)`.

Printing emits the book's symbols with minimal brackets, and `parse(str(f)) == f`
for every formula — that round trip is a test, and it is what keeps the printer
and the parser from drifting apart.

### Notation

| Typed | Read as | Also accepted |
|---|---|---|
| `~P` | ¬P | `¬P` |
| `P & Q` | P ∧ Q | `P ∧ Q` |
| `P \| Q` | P ∨ Q | `P ∨ Q` |
| `P -> Q` | P → Q | `P → Q` |
| `P <-> Q` | P ↔ Q | `P ↔ Q` |
| `Ax Fx` | ∀x Fx | `∀x Fx` |
| `Ex Fx` | ∃x Fx | `∃x Fx` |
| `a=b` | a = b | |

Terms are decided by letter: **`u`–`z` are variables, `a`–`t` are constants**,
either with an optional `_n` subscript (`x_1`, `a_12`). Uppercase letters are
predicates, applied by juxtaposition (`Rxy`) or with brackets (`R(x, y)`).

Two consequences worth knowing. A name longer than one letter needs the bracketed
form — `Loves(a, b)`, never `Lovesab`. And bare `A` and `E` are the quantifiers,
so a predicate letter `A` must be written `A(x)`; the printer knows this and
brackets it for you.

`¬` binds tightest, then `∧`, then `∨`, then `→` and `↔`, which share a level and
associate to the right. Quantifiers take the smallest scope they can, so
`Ax Fx -> Gx` is `(∀x Fx) → Gx`. Because the two arrows share a level, one nested
directly in the other must be bracketed: `P -> Q <-> S` is a `ParseError`, and
`P -> (Q <-> S)` is what you want.

Errors point at the character they stopped on:

```
>>> parse("P -> Q <-> S")
ParseError: mixing → and ↔ needs brackets (column 8)

  P -> Q <-> S
         ^
```

## Proofs

Applying a rule *is* building the proof: each rule is a class, and constructing
it checks that the rule applies. If you are holding a `Proof`, it is a proof.

```python
p = parse("P")
theorem = ImpliesIntro(Assumption(p), p)

theorem.conclusion       # P → P
theorem.assumptions      # frozenset() — nothing left undischarged
theorem.is_theorem()     # True
theorem.length()         # 2, the longest branch
```

`assumptions` is `As(π)`, the sentences the conclusion still rests on. It is a
set of **sentences**, not of nodes, which is the book's convention and has a
consequence worth stating: one discharge closes every leaf carrying that
sentence.

```python
both = AndIntro(Assumption(p), Assumption(p))
both.assumptions                          # frozenset({P}) — one assumption
len(list(both.leaves()))                  # 2 — two leaves
ImpliesIntro(both, p).assumptions         # frozenset() — one step closed both
```

Rules that discharge are told what to discharge, since it need not occur in the
subproof at all, and rules that add material are told what to add:

```python
ImpliesIntro(proof, assumption)   # ψ → φ, discharging ψ
OrIntro1(proof, right)            # φ ∨ right
NotIntro(pi1, pi2, assumption)    # ¬φ, from a contradictory pair
NotElim(pi1, pi2, conclusion)     # φ, discharging ¬φ
```

There is no absurdity sign. Halbach's negation rules act on a contradictory pair
ψ / ¬ψ directly and yield a negation, so `⊥` is not part of the language.

### The quantifier rules

The quantifier rules use **constants as parameters**, so every line of a proof is
a sentence. `∀Intro` generalises on a constant that must be *arbitrary* — absent
from every assumption still open:

```python
x, a = Variable("x"), Constant("a")
major, minor = Assumption(parse("Ax(Fx -> Gx)")), Assumption(parse("Ax Fx"))
step = ImpliesElim(ForallElim(minor, a), ForallElim(major, a))
print(ForallIntro(step, a, x))
```

```
∀x Fx      ∀x(Fx → Gx)
───── ∀E   ─────────── ∀E
 Fa          Fa → Ga
 ─────────────────── →E
         Ga
       ───── ∀I
       ∀x Gx
```

Break the proviso and the refusal names what broke it:

```python
>>> ForallIntro(Assumption(parse("Fa")), a, x)
ProvisoError: ∀Intro: a is not arbitrary: it occurs in the undischarged assumption Fa
```

`∃Intro` and `=Elim` are given their conclusion and check it, rather than
computing one. Both replace *some* occurrences rather than all — from `Raa` you
may infer `∃x Rxa`, `∃x Rax` or `∃x Rxx`, and nothing in the premise says which
you meant:

```python
raa = Assumption(parse("Raa"))
ExistsIntro(raa, parse("Ex Rxa"))    # fine
ExistsIntro(raa, parse("Ex Rxx"))    # also fine
ExistsIntro(raa, parse("Ex Rxb"))    # MismatchError
```

### The rules

| | Introduction | Elimination |
|---|---|---|
| leaves | `Assumption`, `EqualityIntro` | |
| ∧ | `AndIntro` | `AndElim1`, `AndElim2` |
| ∨ | `OrIntro1`, `OrIntro2` | `OrElim` |
| → | `ImpliesIntro` | `ImpliesElim` |
| ¬ | `NotIntro` | `NotElim` |
| ↔ | `IffIntro` | `IffElim1`, `IffElim2` |
| ∀ | `ForallIntro` | `ForallElim` |
| ∃ | `ExistsIntro` | `ExistsElim` |
| = | `EqualityIntro` | `EqualityElim1`, `EqualityElim2` |

Constructor arguments follow the numbering of the subproofs in
`reference/NDrules.pdf`, so each rule reads off its diagram there. Two are
worth flagging: `IffIntro(π₁, π₂)` takes the proof of the *right* half first,
and `OrElim(π₁, π₂, π₃)` takes the disjunction last.

Rules can also be reached by name, which is how a user interface would enumerate
them without importing every class:

```python
rule_catalogue()                                   # all 21 classes
apply("∧Intro", [Assumption(p), Assumption(parse("Q"))])   # build one
can_apply("∧Elim1", [Assumption(p)])               # the error, without raising
rule("∃Intro").parameters                          # what else it needs
```

`can_apply` is `apply` in a `try`, so the two can never disagree about whether a
rule is available.

## Drawing

`print(proof)` draws the tree. Discharged assumptions are bracketed and numbered
with the step that discharged them; numbers grow as the eye travels down the page,
and a discharge that closes nothing gets no number.

`to_text(proof, ascii_only=True)` draws the bars with hyphens for terminals that
mangle box-drawing characters. Underneath, `layout(proof)` returns the placement
as data — every sentence and bar with its position and width — so the drawing can
be redone with something other than characters.

## Tests

```sh
python3 -m unittest discover -s tests -t .          # 206 tests
python3 -m unittest tests.test_rules                # one module
python3 demo.py                                     # a printable tour
```

`demo.py` sits outside the package on purpose: running a module of `nd` as
`__main__` would import it a second time under its real name, giving two copies
of every class, and equality between them would silently fail.

## A note on the reference

`reference/NDrules.pdf` sets out the system formally. The checker follows it
except in one place: its statement of (∃Elim) on p.45 omits the requirement that
the parameter not occur in the conclusion. Without that, `∃x Fx ⊢ Fa` is
derivable — take the subproof to be the bare assumption `Fa`, and every stated
condition holds vacuously. *The Logic Manual* states the proviso with the
conclusion included, and that is what is enforced here.

## Layout

```
nd/formula.py    terms and formulae; substitution, generalisation, α-equivalence
nd/parser.py     reading the book's notation from strings
nd/proofs.py     the proof tree, the errors, the rule registry
nd/rules.py      the 21 rules and their provisos
nd/render.py     placement and drawing
```

`CLAUDE.md` records the design decisions and the reasons behind them.
