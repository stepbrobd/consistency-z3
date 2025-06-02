import z3

from consistency.abstract_execution import AbstractExecution as AE
from consistency.common import compose
from consistency.history import History as H
from consistency.model.model import Model
from consistency.model.monotonic_reads import MonotonicReads
from consistency.model.monotonic_writes import MonotonicWrites
from consistency.model.pram_consistency import PRAMConsistency
from consistency.model.read_your_writes import ReadYourWrites
from consistency.model.rval import RVal
from consistency.model.writes_follow_reads import WritesFollowReads
from consistency.operation import Operation as Op


class Linearizability(Model):
    @staticmethod
    def assertions(symbols: list[str] | None = None) -> z3.BoolRef:
        if symbols is None:
            symbols = ["a", "b", "c", "x"]
        decl = " ".join(symbols)

        _, (rd, wr) = Op.Sort()
        op = Op.Create()
        a, b, *_ = Op.Consts(decl)

        rb = H.Relation.returns_before(symbols)
        vis = AE.Relation.visibility(symbols)
        ar = AE.Relation.arbitration(symbols)

        # single order imposes a single global order that defines both visibility and arbitration
        # non-transactional pp.8
        # principles of eventual consistency pp.59
        single_order = z3.ForAll(
            [a, b],
            z3.And(
                z3.Implies(vis(a, b), ar(a, b)),
                z3.Implies(z3.And(ar(a, b), op.returned(a) == z3.Bool(True)), vis(a, b)),  # type: ignore
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
            z3.BoolVal(True),
        )

        # return value consistency specifies the return value consistency of a replicated data type
        rval = RVal.assertions(symbols, AE.Relation.can_view(symbols))

        return compose(
            z3.And(single_order, real_time, rval),  # type: ignore
            MonotonicReads.assertions(),
            MonotonicWrites.assertions(),
            WritesFollowReads.assertions(),
            ReadYourWrites.assertions(),
            PRAMConsistency.assertions(),
       )
