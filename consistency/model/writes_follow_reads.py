import z3

from consistency.constraint import Constraint


class WritesFollowReads:
    """
    Writes Follow Reads are defined as:
    for all write operations $a, c$ in history, a set of operations denoted by $H$, and,
    for all read operation $b$ in history $H$,
    if operation $a$ is visible to operation $b$, and $b$ returns before $c$ starts within the same session,
    then operation $a$ must precede operation $c$ in the total order imposed by arbitration.
    """
    @staticmethod
    def constraints(s: z3.Solver) -> None:
        _, (rd, wr) = Constraint.declare_operation_type()
        op = Constraint.declare_operation()
        a, b, c = Constraint.declare_operation_symbols("a b c")

        so = Constraint.session_order(s)
        vis = Constraint.visibility(s)
        ar = Constraint.arbitration(s)

        # writes follow reads
        s.add(z3.ForAll([a, b, c],
                z3.Implies(
                    z3.And(vis(a, b), so(b, c), op.type(a) == wr, op.type(c) == wr, op.type(b) == rd),
                    ar(a, c)
                )
        ))
