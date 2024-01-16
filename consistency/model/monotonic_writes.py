import z3

from consistency.abstract_execution import AbstractExecution
from consistency.constraint import Constraint


class MonotonicWrites:
    """
    Monotonic Writes are defined as:
    for all write operations $a, b$ in history, a set of operations denoted by $H$,
    if operation $a$ returns before $b$ starts, and $a,b$ are in the same session,
    then operation $a$ must precede operation $b$ in the total order imposed by arbitration.
    """
    @staticmethod
    def constraints(s: z3.Solver) -> None:
        _, (rd, wr) = Constraint.declare_operation_type()
        op = Constraint.declare_operation()
        a, b = Constraint.declare_operation_symbols("a b")

        so = Constraint.session_order(s)
        ar = Constraint.arbitration(s)

        # monotonic writes
        s.add(z3.ForAll([a, b],
                z3.Implies(
                    z3.And(so(a, b), op.type(a) == wr, op.type(b) == wr),
                    ar(a, b)
                )
        ))


    @staticmethod
    def check(ae: AbstractExecution) -> bool:
        ...
