import z3

from consistency.abstract_execution import AbstractExecution as AE
from consistency.history import History as H
from consistency.operation import Operation as Op


class Linearizability:
    """
    Incomplete
    Too strong, standalone check will fail but the compatibility will pass as expected
    """
    @staticmethod
    def assertions() -> z3.BoolRef:
        # single order imposes a single global order that defines both visibility and arbitration (very strong, probably can't be modeled)
        # real time constrains arbitration to comply to the returns-before partial ordering
        # return value consistency specifies the return value consistency of a replicated data type

        _, (rd, wr) = Op.Sort()
        op = Op.Create()
        a, b = Op.Consts("a b")

        rb = H.Relation.returns_before()
        H.Relation.same_session()
        so = H.Relation.session_order()
        vis = AE.Relation.visibility()
        ar = AE.Relation.arbitration()

        # single order
        single_order = z3.ForAll([a, b],
            z3.If(z3.And(op.type(a) == wr, op.type(b) == wr),
                z3.Or(
                    z3.And(so(a, b), ar(a, b), vis(a, b)),
                    z3.And(so(b, a), ar(b, a), vis(b, a))
                ),
                z3.BoolVal(True)
            )
        )

        # real time: ar comply to rb or fail
        # the non-transaction paper made a mistake at pp.8 formula 9 (swapped rb and ar)
        # however, due to arbitration is defined too relaxed in our code, swapping rb(a, b) with ar(a, b) will still satisfy the constraint
        real_time = z3.If(z3.And(ar(a, b), op.type(a) == wr, op.type(b) == wr), # only arbitrate ar, must add this condition or z3 will hang
                rb(a, b),
                z3.BoolVal(False)
        )

        # rval is context dependent, skipped for now (see pp. 5)
        rval = z3.BoolVal(True)

        return z3.And(single_order, real_time, rval)
