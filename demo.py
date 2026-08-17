"""A printable tour of the language layer: ``python3 demo.py``.

Kept outside the ``nd`` package deliberately.  Running a module of the
package as ``__main__`` would import it a second time under its real
name, giving two copies of every class, and the dataclass ``__eq__``
requires an identical class -- so the equality checks below would report
False for formulae that are in fact the same.
"""

from nd import (
    And,
    Atom,
    CaptureError,
    Constant,
    Equality,
    Exists,
    Forall,
    Formula,
    Iff,
    Implies,
    Not,
    Or,
    ParseError,
    Variable,
    parse,
)


def main() -> None:
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


if __name__ == "__main__":
    main()
