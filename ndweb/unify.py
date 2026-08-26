"""Filling in the slots a half-built block leaves empty.

A block on the sheet is a rule with three sorts of slot: the premises
above the bar, the parameters the rule needs besides them, and the
conclusion below.  A student may write in any of them, in any order, and
the rest of the block should say what it can about the others.  Working
out those consequences is all this module does.

It runs in both directions and neither is new:

**Downwards** is the engine.  Given the premises and the parameters,
``apply`` already computes the conclusion, and rather than write a second
table predicting one, the premises are stood up as bare assumptions and
the real rule is applied to them.  A premise slot holding ``φ`` with
nothing above it *is* an assumption of ``φ``, so this is not a simulation
of the rule -- it is the rule, on the proof as it currently stands.

**Upwards** is :mod:`ndweb.refine`, which already turns a goal into the
subgoals that would establish it.  What is added here is only where its
inputs come from: in the editor they are the premises and parameters the
student has already written, so the block completes itself instead of
stopping to ask.

Two rules need a word.  ``∀Intro`` and ``∃Elim`` carry provisos about a
parameter being arbitrary or fresh, and those are conditions on the whole
subtree -- an assumption still open three steps up can break them.  While
the branches above are unfinished the provisos are therefore *unsettled*
rather than broken, and refusing to show a conclusion on that basis would
mean the block stayed blank until the moment it was finished.  So for
those two, and only those two, a proviso failure during prediction falls
back to the conclusion the rule would reach.  Nothing is proved by it:
:mod:`ndweb.realise` applies the same rule to the real subproofs and lets
the proviso bite for real.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Dict, FrozenSet, List, Optional, Tuple

from nd.formula import Formula, Implies, Variable
from nd.proofs import rule

from ndweb.attempt import RuleFailure, attempt
from ndweb.derivation import Node, Step, expected, kwargs, walk
from ndweb.discharge import discharges
from ndweb.refine import Context, RefineError, fields, refine

__all__ = ["Solved", "solve", "predict"]

#: Where a rule's backward question is answered by a premise the student
#: has already written.  ``refine`` asks for the antecedent of a ``→Elim``;
#: on the sheet that antecedent is the left-hand premise slot, so if it has
#: been filled in there is nothing to ask.  Keyed by rule, then by the name
#: ``ndweb.refine.fields`` uses, giving the index of the premise that
#: answers it.
FROM_PREMISE = {
    "∧Elim": {"conjunction": 0},
    "∨Intro": {"disjunct": 0},
    "→Elim": {"antecedent": 0},
    "∨Elim": {"disjunction": 2},
    "¬Intro": {"witness": 0},
    "¬Elim": {"witness": 0},
    "↔Elim": {"biconditional": 0},
    "∀Elim": {"universal": 0},
    "∃Elim": {"existential": 0},
    "=Elim1": {"identity": 0, "source": 1},
    "=Elim2": {"identity": 0, "source": 1},
}

#: The premise that settles an elimination on its own.  ``→Elim`` given
#: only its conditional already knows both what it concludes and what its
#: other premise must be, and saying so is most of what makes the sheet
#: feel as though it is helping.  Each entry is the index of that premise,
#: the shape it must have, and what the rest of the block then is: the
#: conclusion, and the other premises by index.
#:
#: ``↔Elim`` used to be here twice and cannot be here at all: one rule taking
#: either half of the biconditional does not know, from ``φ ↔ ψ`` alone, which
#: half it is being given.  Write either the other premise or the conclusion
#: and the block still completes itself -- through ``predict`` one way and
#: ``refine`` the other -- it just has nothing to say before then.
MAJOR = {
    "→Elim": (1, Implies, lambda f: (f.right, {0: f.left})),
}

#: Premises that simply repeat the conclusion, whatever else is unknown.
#:
#: ``∨Elim`` argues for the same χ in both cases and ``∃Elim``'s second
#: subproof reaches the χ it concludes, so dropping either on a goal can
#: fill those slots at once -- before anything is known about the
#: disjunction or the existential, which is the part the student supplies.
#: ``tests/test_unify.py`` checks this against the figures in
#: :data:`ndweb.catalogue.SCHEMA`, so the picture and the behaviour cannot
#: come apart.
MIRRORS = {
    "∨Elim": (0, 1),
    "∃Elim": (1,),
}

#: How many times to run the two directions against each other.  Filling a
#: conclusion downwards can unblock a premise upwards and the other way
#: about, but no rule chains further than a couple of rounds, and a bound
#: is cheaper than detecting a fixed point.
ROUNDS = 3


@dataclass(frozen=True)
class Solved:
    """What could be worked out about one tree.

    ``formulas`` gives every node the sentence it concludes, whether it was
    written there or followed from elsewhere; ``params`` gives every step
    the keywords it would be applied with; ``available`` says what may be
    assumed at each node.  All three are recomputed from the tree on every
    edit and none of them is stored in the document.
    """

    formulas: Dict[int, Formula] = field(default_factory=dict)
    params: Dict[int, Dict[str, object]] = field(default_factory=dict)
    available: Dict[int, FrozenSet[Formula]] = field(default_factory=dict)
    written: FrozenSet[int] = frozenset()
    notes: Dict[int, Tuple[str, ...]] = field(default_factory=dict)
    failures: Dict[int, RuleFailure] = field(default_factory=dict)

    def formula(self, node_id: int) -> Optional[Formula]:
        return self.formulas.get(node_id)

    def is_written(self, node_id: int) -> bool:
        """Whether this sentence was typed rather than worked out."""
        return node_id in self.written


def solve(root: Node, available: FrozenSet[Formula] = frozenset()) -> Solved:
    """Work out everything the block's own shape settles."""
    formulas: Dict[int, Formula] = {}
    params: Dict[int, Dict[str, object]] = {}
    notes: Dict[int, Tuple[str, ...]] = {}
    failures: Dict[int, RuleFailure] = {}
    written = set()

    for node in walk(root):
        written_here = expected(node)
        if written_here is not None:
            formulas[node.id] = written_here
            written.add(node.id)
        if isinstance(node, Step):
            params[node.id] = kwargs(node)

    scopes: Dict[int, FrozenSet[Formula]] = {}
    for _ in range(ROUNDS):
        before = (dict(formulas), _snapshot(params))
        scopes = _scopes(root, available, formulas, params)
        for node in walk(root):  # children first
            if isinstance(node, Step):
                _downwards(node, formulas, params, failures)
        scopes = _scopes(root, available, formulas, params)
        for node in _top_down(root):
            if isinstance(node, Step):
                _upwards(node, formulas, params, notes, scopes)
        if before == (formulas, _snapshot(params)):
            break

    return Solved(formulas, params, scopes, frozenset(written), notes, failures)


def predict(
    rule_name: str, premises: List[Formula], values: Dict[str, object]
) -> Tuple[Optional[Formula], Optional[RuleFailure]]:
    """What this rule concludes from these sentences, if it concludes.

    The premises are stood up as assumptions and the rule applied, so this
    is the engine's answer rather than a second opinion about it.
    """
    leaves = []
    for premise in premises:
        made = attempt("Assumption", (), formula=premise)
        if not made.ok:
            return None, made.failure
        leaves.append(made.proof)

    outcome = attempt(rule_name, leaves, **values)
    if outcome.ok:
        return outcome.proof.conclusion, None
    if outcome.failure.kind == "proviso" and rule_name in _UNSETTLED:
        try:
            return _UNSETTLED[rule_name](premises, values), None
        except (KeyError, IndexError, AttributeError, TypeError, ValueError):
            return None, outcome.failure
    return None, outcome.failure


#: The two rules whose provisos cannot be settled until the branches above
#: them are finished, and the conclusion each would reach.  See the module
#: docstring: this predicts, it does not prove.
_UNSETTLED = {
    "∀Intro": lambda premises, values: premises[0].generalise(
        values["constant"], values["variable"]
    ),
    "∃Elim": lambda premises, values: premises[1],
}


# -- the two directions ----------------------------------------------------


def _downwards(
    step: Step,
    formulas: Dict[int, Formula],
    params: Dict[int, Dict[str, object]],
    failures: Dict[int, RuleFailure],
) -> None:
    """From premises and parameters to a conclusion."""
    premises = [formulas.get(child.id) for child in step.children]
    _decompose(step, premises, formulas)
    if any(premise is None for premise in premises):
        return
    values = params.setdefault(step.id, {})
    _defaults(step.rule, premises, values)
    if _missing(step.rule, values):
        return
    if step.id in formulas:
        return

    conclusion, failure = predict(step.rule, premises, values)
    if conclusion is not None:
        formulas[step.id] = conclusion
        failures.pop(step.id, None)
    elif failure is not None:
        failures[step.id] = failure


def _upwards(
    step: Step,
    formulas: Dict[int, Formula],
    params: Dict[int, Dict[str, object]],
    notes: Dict[int, Tuple[str, ...]],
    scopes: Dict[int, FrozenSet[Formula]],
) -> None:
    """From a conclusion back to the premises that would give it."""
    target = formulas.get(step.id)
    if target is None:
        return

    for index in MIRRORS.get(step.rule, ()):
        if index < len(step.children) and step.children[index].id not in formulas:
            formulas[step.children[index].id] = target

    values = params.setdefault(step.id, {})
    premises = [formulas.get(child.id) for child in step.children]
    if all(p is not None for p in premises) and not _missing(step.rule, values):
        return

    context = Context(available=scopes.get(step.id, frozenset()))
    try:
        wanted = fields(step.rule, target, context)
    except RefineError as error:
        notes[step.id] = (error.message,)
        return

    inputs: Dict[str, object] = {}
    from_premise = FROM_PREMISE.get(step.rule, {})
    for want in wanted:
        index = from_premise.get(want.name)
        found = None
        if index is not None and index < len(premises):
            found = premises[index]
        if found is None:
            found = values.get(want.name)
        if found is None and want.default:
            found = want.default
        if found is not None:
            inputs[want.name] = found

    try:
        refinement = refine(step.rule, target, context, inputs)
    except RefineError as error:
        notes[step.id] = (error.message,)
        return

    notes[step.id] = refinement.warnings
    if len(refinement.subgoals) == len(step.children):
        for child, subgoal in zip(step.children, refinement.subgoals):
            if child.id not in formulas:
                formulas[child.id] = subgoal.target
    for binding in refinement.params:
        if values.get(binding.name) is None:
            values[binding.name] = binding.value


def _decompose(step: Step, premises: List[Optional[Formula]],
               formulas: Dict[int, Formula]) -> None:
    """Read the rest of an elimination off its major premise."""
    entry = MAJOR.get(step.rule)
    if entry is None:
        return
    index, shape, split = entry
    if index >= len(premises):
        return
    major = premises[index]
    if not isinstance(major, shape):
        return
    conclusion, others = split(major)
    if step.id not in formulas:
        formulas[step.id] = conclusion
    for at, formula in others.items():
        if at < len(step.children) and step.children[at].id not in formulas:
            formulas[step.children[at].id] = formula
            premises[at] = formula


def _defaults(rule_name: str, premises: List[Formula],
              values: Dict[str, object]) -> None:
    """Choices a student would only ever make one way.

    Only ``∀Intro``'s bound variable qualifies.  Which constant to
    generalise on is a real decision and is left alone; what to call the
    variable that replaces it is not, and asking would be pedantry.
    """
    if rule_name != "∀Intro" or values.get("variable") is not None:
        return
    if values.get("constant") is None or not premises:
        return
    for name in ("x", "y", "z", "u", "v", "w"):
        candidate = Variable(name)
        try:
            premises[0].generalise(values["constant"], candidate)
        except Exception:
            continue
        values["variable"] = candidate
        return


# -- housekeeping ----------------------------------------------------------


def _missing(rule_name: str, values: Dict[str, object]) -> List[str]:
    """Required parameters this step has not been given."""
    try:
        declared = rule(rule_name).parameters
    except KeyError:
        return []
    return [p.name for p in declared if p.required and values.get(p.name) is None]


def _top_down(root: Node) -> List[Node]:
    found: List[Node] = []
    pending = [root]
    while pending:
        node = pending.pop(0)
        found.append(node)
        if isinstance(node, Step):
            pending.extend(node.children)
    return found


def _scopes(
    root: Node,
    available: FrozenSet[Formula],
    formulas: Dict[int, Formula],
    params: Dict[int, Dict[str, object]],
) -> Dict[int, FrozenSet[Formula]]:
    """What may be assumed at each node, given what is known so far."""
    found: Dict[int, FrozenSet[Formula]] = {}

    def resolve(node: Node) -> Optional[Formula]:
        return formulas.get(node.id)

    def descend(node: Node, scope: FrozenSet[Formula]) -> None:
        found[node.id] = scope
        if isinstance(node, Step):
            closed = discharges(node, resolve, params.get(node.id))
            for child, group in zip(node.children, closed):
                descend(child, scope | group)

    descend(root, available)
    return found


def _snapshot(params: Dict[int, Dict[str, object]]) -> Dict[int, Dict[str, object]]:
    return dict((key, dict(value)) for key, value in params.items())
