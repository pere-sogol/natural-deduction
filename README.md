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

The language, the parser, all 17 rules and the renderer are written and tested,
and there is a browser sandbox built on top of them — see **The sandbox** below.
There is still no proof *search*: the sandbox works out everything a block's own
shape settles, and tells you why a step will not go, but it will not find the
proof for you.

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
OrIntro(proof, conclusion)        # the disjunction claimed, φ as one half
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
| ∧ | `AndIntro` | `AndElim` |
| ∨ | `OrIntro` | `OrElim` |
| → | `ImpliesIntro` | `ImpliesElim` |
| ¬ | `NotIntro` | `NotElim` |
| ↔ | `IffIntro` | `IffElim` |
| ∀ | `ForallIntro` | `ForallElim` |
| ∃ | `ExistsIntro` | `ExistsElim` |
| = | `EqualityIntro` | `EqualityElim` |

Constructor arguments follow the numbering of the subproofs in
`reference/NDrules.pdf`, so each rule reads off its diagram there. Two are
worth flagging: `IffIntro(π₁, π₂)` takes the proof of the *right* half first,
and `OrElim(π₁, π₂, π₃)` takes the disjunction last.

`AndElim`, `OrIntro`, `IffElim` and `EqualityElim` are each one rule where the
reference has two. Three of them are told what they conclude —
`AndElim(π, parse("Q"))`, `OrIntro(π, parse("P | Q"))` — and `IffElim` reads its
direction off the half it is given, so it needs nothing. See the note on the
reference below.

Rules can also be reached by name, which is how a user interface would enumerate
them without importing every class:

```python
rule_catalogue()                                   # all 17 classes
apply("∧Intro", [Assumption(p), Assumption(parse("Q"))])   # build one
can_apply("∧Elim", [Assumption(p)], conclusion=p)  # the error, without raising
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
as data — every sentence and bar with its position and width — along with the
discharge numbering, which the browser reuses even though it sets its own type.

## Tests

```sh
python3 -m unittest discover -s tests -t .          # 405 tests
python3 -m unittest tests.test_rules                # one module
python3 demo.py                                     # a printable tour
```

`demo.py` sits outside the package on purpose: running a module of `nd` as
`__main__` would import it a second time under its real name, giving two copies
of every class, and equality between them would silently fail.

## A note on the reference

`reference/NDrules.pdf` sets out the system formally. The checker follows it
except in two places.

Its statement of (∃Elim) on p.45 omits the requirement that the parameter not
occur in the conclusion. Without that, `∃x Fx ⊢ Fa` is derivable — take the
subproof to be the bare assumption `Fa`, and every stated condition holds
vacuously. *The Logic Manual* states the proviso with the conclusion included,
and that is what is enforced here.

Four of its rules are stated as numbered pairs and are single rules here:
(∧Elim1)/(∧Elim2), (∨Intro1)/(∨Intro2), (↔Elim1)/(↔Elim2) and
(=Elim1)/(=Elim2). In each case the two halves differ in nothing a proof
records — the same premises, the same node, the same label on the bar — so a
finished proof could never tell you which was used, and keeping them apart only
meant choosing a side before there was a formula to choose about.

`AndElim`, `OrIntro` and `EqualityElim` are told the sentence they conclude and
check it against the premise; `IffElim` needs nothing at all, since the half you
put above it decides which way it runs. Each proves exactly what its pair
proved.

## The sandbox

A proof sandbox that runs entirely in the browser — no server, no build step,
nothing to install.

```sh
python3 -m web.serve        # serves the repo and opens the sandbox
```

Pyodide loads this package into WebAssembly, so the checker doing the marking is
the one these tests cover, not a reimplementation that could drift from it.
First visit fetches about 5 MB of Python and takes a few seconds; after that the
browser has it cached.

**Drag any rule onto the sheet.** It lands with every slot empty — the premises
above the bar, the conclusion below, and whatever else the rule needs as a small
labelled chip. Nothing is asked for in advance and nothing has to be decided
first.

**Then write in whichever slot you know.** The rest of the block works itself
out, in both directions and from either end:

| You write | The block works out |
|---|---|
| `P` and `Q` above a `∧I` | `P ∧ Q` below it |
| `P ∧ Q` below a `∧I` | `P` and `Q` above it |
| `P → Q` in the right premise of `→E` | `P` on the left, `Q` below |
| `P` on the left of `→E`, `Q` below | `P → Q` on the right |
| `P → Q` under a `→I` | the subgoal `Q`, and `P` marked as discharged |

Whatever a block cannot settle stays an empty slot, because nothing is invented:
`↔E` concluding `ψ` says nothing about which `φ` it came through, so it waits.
Sentences you wrote are set in black, sentences the sheet worked out in grey.

**Blocks join up.** Drag one onto an empty slot in another and it plugs in; drag
a bar to pull that branch back off, leaving a slot that remembers what it said.
A block that proves the wrong thing still goes in — its bar then tells you what
it actually proves, which is more use than refusing it.

Working downwards is the engine itself, not a second opinion about it: a premise
slot holding `φ` with nothing above it *is* an assumption of `φ`, so the sheet
applies the real rule to the proof as it stands. Working upwards is a heuristic,
and is allowed to be unhelpful — every proof the sandbox holds was built by
`apply()`, so a bad suggestion can waste your time but cannot get a bad proof
past the checker.

Rules that cannot conclude the selected slot are dimmed with the reason on
hover, and can still be dropped. Hovering an inference lights up every leaf it
discharges, since one step closes them all. Undo, redo, and a link that carries
the whole sheet in its fragment all come free from the document being immutable.

### Typesetting

Proofs are set, not drawn. Each inference is a column — premises in a row, a
bar, a conclusion centred under it — so every box takes the width of what is in
it and the figure reflows as sentences grow. The sentences themselves are cut
into classified pieces in Python, letters italic and connectives upright with
proper space around them, the way a logic text sets them.

Underneath, `layout()` is still run for one thing: the book's discharge
numbering, which is subtle enough to be worth having exactly once. The placement
is thrown away and the numbers kept.

## Layout

```
nd/formula.py    terms and formulae; substitution, generalisation, α-equivalence
nd/parser.py     reading the book's notation from strings
nd/proofs.py     the proof tree, the errors, the rule registry
nd/rules.py      the 17 rules and their provisos
nd/render.py     placement and drawing

ndweb/           the sandbox's model: slots, both directions of every rule,
                 and a proof as a nesting rather than a grid
web/             the page itself; bootstrap.py is what Pyodide runs
```

`CLAUDE.md` records the design decisions and the reasons behind them.
