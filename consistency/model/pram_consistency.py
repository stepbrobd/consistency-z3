import z3

from consistency.abstract_execution import AbstractExecution as AE
from consistency.history import History as H
from consistency.model.model import Model
from consistency.operation import Operation as Op


class PRAMConsistency(Model):
    """
    PRAM consistency is defined as:
    for all operations $a$ and $b$ in history, a set of operations denoted by $H$,
    if operation $a$ returns before $b$ starts, and $a,b$ are in the same session,
    then operation $a$ is visible to operation $b$.
    """
    @staticmethod
    def assertions(symbols: list[str] | None = None) -> z3.BoolRef:
        if symbols is None:
            symbols = ["a", "b"]
        decl = " ".join(symbols)

        # _, (rd, wr) = Op.Sort()
        # op = Op.Create()
        a, b, *_ = Op.Consts(decl)

        so = H.Relation.session_order()
        ar = AE.Relation.arbitration()
        vis = AE.Relation.visibility()

        # PRAM consistency
        return z3.ForAll([a, b],
            z3.Implies(
                so(a, b),
                z3.And(vis(a, b), ar(a, b))
            )
        )
