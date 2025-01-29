import z3

from consistency.abstract_execution import AbstractExecution as AE
from consistency.common import cleanup, construct
from consistency.history import History as H
from consistency.model.monotonic_reads import MonotonicReads
from consistency.operation import Operation as Op


@cleanup
def test_visibility_transitivity_under_monotonic_reads() -> None:
    _, (rd, wr) = Op.Sort()
    op = Op.Create()
    a, b, c, d, e, f = Op.Consts("a b c d e f")
    so = H.Relation.session_order()
    vis = AE.Relation.visibility()

    lhs = z3.And(
        MonotonicReads.assertions(),
        op.type(a) == wr,  # type: ignore
        op.type(b) == rd,  # type: ignore
        op.type(c) == wr,  # type: ignore
        op.type(d) == rd,  # type: ignore
        op.type(e) == wr,  # type: ignore
        op.type(f) == rd,  # type: ignore
        vis(a, b),
        so(b, d),
        vis(c, d),
        so(d, f),
    )
    rhs = z3.And(vis(a, d), vis(c, f))
    s = construct(lhs, rhs)  # type: ignore
    assert s.check() == z3.unsat
