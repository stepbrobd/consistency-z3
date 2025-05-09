import z3

from consistency.abstract_execution import AbstractExecution as AE
from consistency.history import History as H
from consistency.model.model import Model
from consistency.operation import Operation as Op


class MonotonicReads(Model):
    """
    Monotonic Reads are defined as:
    for all operations $a$ in history, a set of operations denoted by $H$, and,
    for all read operations $b$ and $c$ in history $H$,
    if operation $a$ is visible to operation $b$, $b$ returns before $c$ starts, and $b, c$ are in the same session,
    then operation $a$ is visible to operation $c$.
    """

    @staticmethod
    def assertions(symbols: list[str] | None = None) -> z3.BoolRef:
        """
        Add monotonic read constraints.
        """
        if symbols is None:
            symbols = ["a", "b", "c", "x"]
        decl = " ".join(symbols)

        op = Op.Create()
        _, (rd, wr) = Op.Sort()
        a, b, c, *_ = Op.Consts(decl)

        so = H.Relation.session_order(symbols)
        vis = AE.Relation.visibility(symbols)

        # monotonic read
        return z3.And(  # type: ignore
            # (a -vis-> b /\ b --so-> c) -> a -vis-> c
            z3.ForAll(
                [a, b, c],
                z3.Implies(
                    z3.And(
                        op.type(b) == rd,  # type: ignore
                        op.type(c) == rd,  # type: ignore
                        vis(a, b),
                        so(b, c),
                    ),
                    vis(a, c),
                ),
            ),
            # monotonically increase
            # for example:
            # |---wr(a)---|
            #               |-------wr(b)-------|
            #                |-rd(b)-| |-rd(a)-|
            # a write operation writes a key k to value a
            # after the op returns, a long write operation writes the key k to value b
            # at the same time, two read operations read the key k
            # the first one return b, but the second one return a
            # this is a violation of monotonicity
            # z3.ForAll([a, b],
            #
            # )
        )
