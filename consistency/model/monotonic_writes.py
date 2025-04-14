import z3

from consistency.abstract_execution import AbstractExecution as AE
from consistency.history import History as H
from consistency.model.model import Model
from consistency.operation import Operation as Op


class MonotonicWrites(Model):
    """
    Monotonic Writes are defined as:
    for all write operations $a, b$ in history, a set of operations denoted by $H$,
    if operation $a$ returns before $b$ starts, and $a,b$ are in the same session,
    then operation $a$ must precede operation $b$ in the total order imposed by arbitration.
    """
    @staticmethod
    def assertions(symbols: list[str] | None = None) -> z3.BoolRef:
        if symbols is None:
            symbols = ["a", "b"]
        decl = " ".join(symbols)

        _, (rd, wr) = Op.Sort()
        op = Op.Create()
        a, b, *_ = Op.Consts(decl)

        so = H.Relation.session_order()
        ar = AE.Relation.arbitration()

        # monotonic writes
        return z3.ForAll([a, b],
            z3.If(z3.And(op.type(a) == wr, op.type(b) == wr), # type: ignore
                z3.Implies(
                    so(a, b),
                    ar(a, b)
                ),
                z3.BoolVal(True)
            )
        )
