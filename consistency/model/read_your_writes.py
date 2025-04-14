import z3

from consistency.abstract_execution import AbstractExecution as AE
from consistency.history import History as H
from consistency.model.model import Model
from consistency.operation import Operation as Op


class ReadYourWrites(Model):
    """
    Read-Your-Writes are defined as:
    for all write operations $a$ in history, a set of operations denoted by $H$, and,
    for all read operations $b$ in history $H$,
    if operation $a$ returns before $b$ starts, and $a,b$ are in the same session,
    then operation $a$ is visible to operation $b$.
    """
    @staticmethod
    def assertions(symbols: list[str] | None = None) -> z3.BoolRef:
        """
        Add read-your-writes constraints.
        """
        if symbols is None:
            symbols = ["a", "b"]
        decl = " ".join(symbols)

        _, (rd, wr) = Op.Sort()
        op = Op.Create()
        a, b, *_ = Op.Consts(decl)

        so = H.Relation.session_order()
        vis = AE.Relation.visibility()

        # read-your-writes
        return z3.ForAll([a, b],
                z3.Implies(
                    z3.And(so(a, b), op.type(a) == wr, op.type(b) == rd), # type: ignore
                    vis(a, b)
                )
        )
