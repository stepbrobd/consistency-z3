import z3

from consistency.abstract_execution import AbstractExecution as AE
from consistency.history import History as H
from consistency.operation import Operation as Op


class ReadYourWrites:
    """
    Read-Your-Writes are defined as:
    for all write operations $a$ in history, a set of operations denoted by $H$, and,
    for all read operations $b$ in history $H$,
    if operation $a$ returns before $b$ starts, and $a,b$ are in the same session,
    then operation $a$ is visible to operation $b$.
    """
    @staticmethod
    def assertions() -> z3.BoolRef:
        """
        Add read-your-writes constraints.
        """
        _, (rd, wr) = Op.Sort()
        op = Op.Create()
        a, b = Op.Consts("a b")

        so = H.Relation.session_order()
        vis = AE.Relation.visibility()

        # read-your-writes
        return z3.ForAll([a, b],
                z3.Implies(
                    z3.And(so(a, b), op.type(a) == wr, op.type(b) == rd),
                    vis(a, b)
                )
        )
