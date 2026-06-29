import z3

from consistency.abstract_execution import AbstractExecution as AE
from consistency.model.model import Model
from consistency.operation import Operation as Op


class RVal(Model):
    """
    RVal(F) is context dependent, takes in a binary relation F and returns a boolean value.
    principals of Eventual Consistency pp.49,50
    """

    @staticmethod
    def assertions(  # ty: ignore[missing-override-decorator]
        symbols: list[str] | None = None, f: z3.FuncDeclRef | None = None
    ) -> z3.BoolRef:  # type: ignore
        if f is None:
            raise ValueError("RVal requires a binary relation F")

        if symbols is None:
            symbols = ["a", "b", "c", "x"]
        decl = " ".join(symbols)

        _, (rd, wr) = Op.Sort()
        Op.Create()
        a, b, c, x, *_ = Op.Consts(decl)

        ar = AE.Relation.arbitration(symbols)
        vis = AE.Relation.visibility(symbols)

        # vis^-1 at principals of eventual consistency pp.21
        def visi(arg1: z3.AstRef, arg2: z3.AstRef) -> z3.FuncDeclRef:
            return vis(arg2, arg1)  # vis^-1

        return z3.And(
            # F_reg non-transactional pp.6
            # distributed registers (last write wins)
            # z3.Exists(
            #     [c],
            #     z3.And(ar(c, x), op.type(c) == wr, op.type(x) == rd ,op.ival(c) == op.oval(x))
            # ),
            f(x, a),
            visi(x, a),
            vis(a, b),
            ar(a, b),
        )
