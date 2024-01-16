import z3

from consistency.abstract_execution import AbstractExecution
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

        ss = Constraint.same_session(s)
        so = Constraint.session_order(s)
        vis = Constraint.visibility(s)
        ar = Constraint.arbitration(s)

        s.add([
            # all operations and themselves are in the same session
            ss(a, a),
            ss(b, b),
            ss(c, c),
            # writes follow reads
            z3.ForAll([a, b, c],
                z3.Implies(
                    z3.And(vis(a, b), so(b, c), op.type(a) == wr, op.type(c) == wr, op.type(b) == rd),
                    ar(a, c)
                )
            ),
        ])


    @staticmethod
    def check(ae: AbstractExecution) -> bool:
        ...
