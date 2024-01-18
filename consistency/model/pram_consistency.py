import z3

from consistency.abstract_execution import AbstractExecution as AE
from consistency.history import History as H
from consistency.operation import Operation as Op


class PRAMConsistency:
    """
    PRAM consistency is defined as:
    for all operations $a$ and $b$ in history, a set of operations denoted by $H$,
    if operation $a$ returns before $b$ starts, and $a,b$ are in the same session,
    then operation $a$ is visible to operation $b$.
    """

    @staticmethod
    def assertions() -> None:
        a, b = Op.Consts("a b")

        so = H.Relation.session_order()
        vis = AE.Relation.visibility()

        # PRAM consistency
        return z3.ForAll([a, b], z3.Implies(so(a, b), vis(a, b)))
