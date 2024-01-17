import z3

from consistency.constraint import Constraint


class MonotonicReads:
    """
    Monotonic Reads are defined as:
    for all operations $a$ in history, a set of operations denoted by $H$, and,
    for all read operations $b$ and $c$ in history $H$,
    if operation $a$ is visible to operation $b$, $b$ returns before $c$ starts, and $b, c$ are in the same session,
    then operation $a$ is visible to operation $c$.
    """
    @staticmethod
    def constraints(s: z3.Solver) -> None:
        """
        Add monotonic read constraints.
        """
        _, (rd, wr) = Constraint.declare_operation_type()
        op = Constraint.declare_operation()
        a, b, c = Constraint.declare_operation_symbols("a b c")

        so = Constraint.session_order(s)
        vis = Constraint.visibility(s)

        # monotonic read
        s.add(z3.ForAll([a, b, c],
                z3.Implies(
                    z3.And(vis(a, b), so(b, c), op.type(b) == rd, op.type(c) == rd),
                    vis(a, c)
                )
        ))
