import z3

from consistency.abstract_execution import AbstractExecution as AE
from consistency.history import History as H
from consistency.model.model import Model
from consistency.operation import Operation as Op


class Linearizability(Model):
    """
    Incomplete
    Too strong, standalone check will fail but the compatibility will pass as expected
    """

    @staticmethod
    def assertions(symbols: list[str] | None = None) -> z3.BoolRef:
        if symbols is None:
            symbols = ["a", "b", "c", "x"]
        decl = " ".join(symbols)

        _, (rd, wr) = Op.Sort()
        op = Op.Create()
        a, b, *_ = Op.Consts(decl)

        rb = H.Relation.returns_before(symbols)
        so = H.Relation.session_order(symbols)
        vis = AE.Relation.visibility(symbols)
        ar = AE.Relation.arbitration(symbols)

        # single order imposes a single global order that defines both visibility and arbitration (very strong, probably can't be modeled)
        single_order = z3.ForAll(
            [a, b],
            z3.If(
                z3.And(op.type(a) == wr, op.type(b) == wr),  # type: ignore
                z3.Or(
                    z3.And(so(a, b), ar(a, b), vis(a, b)),
                    z3.And(so(b, a), ar(b, a), vis(b, a)),
                ),
                z3.BoolVal(True),
            ),
        )

        # real time constrains arbitration to comply to the returns-before partial ordering
        # ar comply to rb or fail
        # the non-transaction paper made a mistake at pp.8 formula 9 (swapped rb and ar)
        # however, due to arbitration is defined too relaxed in our code, swapping rb(a, b) with ar(a, b) will still satisfy the constraint
        # only arbitrate ar, must add this condition or z3 will hang
        real_time = z3.If(
            z3.And(ar(a, b), op.type(a) == wr, op.type(b) == wr),  # type: ignore
            rb(a, b),
            z3.BoolVal(False),
        )

        # return value consistency specifies the return value consistency of a replicated data type
        # rval is context dependent, skipped for now (see pp. 5)
        rval = z3.BoolVal(True)

        return z3.And(single_order, real_time, rval)  # type: ignore
