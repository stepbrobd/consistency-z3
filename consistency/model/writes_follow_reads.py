import z3

from consistency.abstract_execution import AbstractExecution as AE
from consistency.history import History as H
from consistency.model.model import Model
from consistency.operation import Operation as Op


class WritesFollowReads(Model):
    """
    Writes Follow Reads are defined as:
    for all write operations $a, c$ in history, a set of operations denoted by $H$, and,
    for all read operation $b$ in history $H$,
    if operation $a$ is visible to operation $b$, and $b$ returns before $c$ starts within the same session,
    then operation $a$ must precede operation $c$ in the total order imposed by arbitration.
    """
    @staticmethod
    def assertions(symbols: list[str] | None = None) -> z3.BoolRef:
        if symbols is None:
            symbols = ["a", "b", "c", "x"]
        decl = " ".join(symbols)

        op = Op.Create()
        _, (rd, wr) = Op.Sort()
        a, b, c, *_ = Op.Consts(decl)

        so = H.Relation.session_order(symbols)
        vis = AE.Relation.visibility(symbols)
        ar = AE.Relation.arbitration(symbols)

        # writes follow reads
        return z3.ForAll([a, b, c],
                z3.Implies(
                    z3.And(
                         op.type(a) == wr, # type: ignore
                         op.type(b) == rd, # type: ignore
                         op.type(c) == wr, # type: ignore
                         vis(a, b),
                         so(b, c),
                    ),
                    ar(a, c)
                )
        )
