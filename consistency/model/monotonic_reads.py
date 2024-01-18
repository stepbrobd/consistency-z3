import z3

from consistency.abstract_execution import AbstractExecution as AE
from consistency.history import History as H
from consistency.operation import Operation as Op


class MonotonicReads:
    """
    Monotonic Reads are defined as:
    for all operations $a$ in history, a set of operations denoted by $H$, and,
    for all read operations $b$ and $c$ in history $H$,
    if operation $a$ is visible to operation $b$, $b$ returns before $c$ starts, and $b, c$ are in the same session,
    then operation $a$ is visible to operation $c$.
    """
    @staticmethod
    def assertions() -> z3.BoolRef:
        """
        Add monotonic read constraints.
        """
        _, (rd, wr) = Op.Sort()
        op = Op.Create()
        a, b, c = Op.Consts("a b c")

        so = H.Relation.session_order()
        vis = AE.Relation.visibility()

        # monotonic read
        return z3.ForAll([a, b, c],
                z3.Implies(
                    z3.And(vis(a, b), so(b, c), op.type(b) == rd, op.type(c) == rd),
                    vis(a, c)
                )
        )
