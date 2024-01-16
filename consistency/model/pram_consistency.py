import z3

from consistency.abstract_execution import AbstractExecution
from consistency.constraint import Constraint


class PRAMConsistency:
    """
    PRAM consistency is defined as:
    for all operations $a$ and $b$ in history, a set of operations denoted by $H$,
    if operation $a$ returns before $b$ starts, and $a,b$ are in the same session,
    then operation $a$ is visible to operation $b$.
    """

    @staticmethod
    def constraints(s: z3.Solver) -> None:
        Constraint.declare_operation()
        a, b = Constraint.declare_operation_symbols("a b")

        ss = Constraint.same_session(s)
        so = Constraint.session_order(s)
        vis = Constraint.visibility(s)

        s.add(
            [
                # all operations and themselves are in the same session
                ss(a, a),
                ss(b, b),
                # PRAM consistency
                z3.ForAll([a, b], z3.Implies(so(a, b), vis(a, b))),
            ]
        )

    @staticmethod
    def check(ae: AbstractExecution) -> bool:
        ...
