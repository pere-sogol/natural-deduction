"""A printable tour of the system: ``python3 demo.py``.

Kept outside the ``nd`` package deliberately.  Running a module of the
package as ``__main__`` would import it a second time under its real
name, giving two copies of every class, and the dataclass ``__eq__``
requires an identical class -- so the equality checks below would report
False for formulae that are in fact the same.
"""

from nd import (
    And,
    AndIntro,
    Assumption,
    Atom,
    CaptureError,
    Constant,
    EqualityIntro,
    Equality,
    Exists,
    ExistsElim,
    ExistsIntro,
    Forall,
    ForallElim,
    ForallIntro,
    Formula,
    Iff,
    Implies,
    ImpliesElim,
    ImpliesIntro,
    Not,
    NotElim,
    NotIntro,
    Or,
    OrIntro1,
    OrIntro2,
    ParseError,
    ProofError,
    Variable,
    can_apply,
    parse,
    reset_arities,
    rule_catalogue,
)


def language() -> None:
    """Terms, formulae, substitution and printing."""
    print("=" * 60)
    print("The language")
    print("=" * 60)

    x, y = Variable("x"), Variable("y")
    a, b = Constant("a"), Constant("b")

    # Ax(Fx -> Ey Rxy), built with named constructors ...
    claim = Forall(x, Implies(Atom("F", x), Exists(y, Atom("R", x, y))))
    # ... with operators, where '&', '|' and '~' are available ...
    same = Forall(x, Atom("F", x).implies(Exists(y, Atom("R", x, y))))
    # ... and read from a string.
    parsed = Formula.parse("Ax(Fx -> Ey Rxy)")

    print("formula:            ", claim)
    print("built three ways:   ", claim == same == parsed)
    print("free variables:     ", set(claim.free_variables()) or "none")
    print("is a sentence:      ", claim.is_sentence())

    # Universal elimination, then universal introduction back again.
    instance = claim.body.substitute(x, a)
    print("instance at a:      ", instance)
    print("constants:          ", set(instance.constants()))
    print("generalised:        ", instance.generalise(a, x))

    # The proviso is reported rather than silently repaired.
    trap = parse("Ey ~x=y")
    print("free for x in {0}: {1}".format(trap, trap.is_free_for(y, x)))
    try:
        trap.substitute(x, y)
    except CaptureError as error:
        print("refused:            ", error)

    # Bracketing follows the usual conventions.
    p, q, r = Atom("P"), Atom("Q"), Atom("S")
    print("smallest scope:     ", Implies(Forall(x, Atom("F", x)), Atom("G", a)))
    print("arrows right-assoc: ", Implies(p, Implies(q, r)))
    print("and binds tighter:  ", Implies(And(p, q), r))
    print("brackets needed:    ", And(p, Implies(q, r)))
    print("arrows must not mix:", Implies(p, Iff(q, r)))
    print("negated:            ", Not(Or(p, And(q, r))))

    # Everything the printer emits reads back as the same formula.
    corpus = (claim, Implies(p, Iff(q, r)), Not(Equality(a, b)), Atom("Loves", a, b))
    print("round-trips:        ", all(parse(str(f)) == f for f in corpus))

    # Errors say where they stopped.
    try:
        parse("P -> Q <-> S")
    except ParseError as error:
        print("\n{0}".format(error))


def _show(heading: str, proof) -> None:
    resting = sorted(str(f) for f in proof.assumptions)
    print("\n{0}".format(heading))
    print("{0} |- {1}".format(", ".join(resting) or "(nothing)", proof.conclusion))
    print()
    print(proof)


def deduction() -> None:
    """Proof trees, the rules, and the provisos on the quantifier rules."""
    print()
    print("=" * 60)
    print("Deduction")
    print("=" * 60)
    print("{0} rules: {1}".format(
        len(rule_catalogue()), " ".join(cls.name for cls in rule_catalogue())
    ))

    reset_arities()
    p = parse("P")
    _show("Discharging an assumption:", ImpliesIntro(Assumption(p), p))

    # Excluded middle needs the classical negation rule, which discharges
    # the negation of what it concludes.
    reset_arities()
    excluded = parse("P | ~P")
    denial = Assumption(parse("~(P | ~P)"))
    not_p = NotIntro(OrIntro1(Assumption(parse("P")), parse("~P")), denial, parse("P"))
    _show("Excluded middle:", NotElim(OrIntro2(not_p, parse("P")), denial, excluded))

    # The quantifier rules run through constants, so every line is a
    # sentence and the parameter has to be arbitrary at the point of use.
    reset_arities()
    x, a = Variable("x"), Constant("a")
    major, minor = Assumption(parse("Ax(Fx -> Gx)")), Assumption(parse("Ax Fx"))
    step = ImpliesElim(ForallElim(minor, a), ForallElim(major, a))
    _show("Generalising on an arbitrary parameter:", ForallIntro(step, a, x))

    reset_arities()
    denial = Assumption(parse("Ax ~Fx"))
    contradiction = NotIntro(
        Assumption(parse("Fa")), ForallElim(denial, a), parse("Ax ~Fx")
    )
    _show(
        "Existential elimination:",
        ExistsElim(Assumption(parse("Ex Fx")), contradiction, a),
    )

    reset_arities()
    _show("The identity rules:", ForallIntro(EqualityIntro(a), a, x))

    print("\nRefusals name the proviso that failed:")
    reset_arities()
    for description, thunk in (
        ("generalising on a constant still assumed",
         lambda: ForallIntro(Assumption(parse("Fa")), a, x)),
        ("a parameter that escapes into the conclusion",
         lambda: ExistsElim(Assumption(parse("Ex Fx")), Assumption(parse("Fa")), a)),
        ("an existential the premise does not support",
         lambda: ExistsIntro(Assumption(parse("Fa")), parse("Ex Gx"))),
    ):
        try:
            thunk()
        except ProofError as error:
            print("  {0}:\n    {1}".format(description, error))

    # The same verdict without raising, for a caller offering a choice of
    # rules and explaining why one of them is unavailable.
    reset_arities()
    print("\ncan_apply, for offering rules rather than applying them:")
    print("  ∧Intro:", can_apply(
        "∧Intro", [Assumption(parse("P")), Assumption(parse("Q"))]) or "available")
    print("  ∧Elim1:", can_apply("∧Elim1", [Assumption(parse("P"))]))


def main() -> None:
    language()
    deduction()


if __name__ == "__main__":
    main()
