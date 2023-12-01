from consistency.abstract_execution import AbstractExecution
from consistency.history import History
from consistency.model.monotonic_read import MonotonicRead
from consistency.operation import Operation
from consistency.relation import Relation


def main() -> int:
    op_a = Operation(
        symbol="a",
        proc=1,
        type="wr",
        obj=1,
        ival=("somekey", "somevalue"),
        oval=None,
        stime=0,
        rtime=1,
    )
    op_b = Operation(
        symbol="b",
        proc=2,
        type="rd",
        obj=1,
        ival="somekey",
        oval="somevalue",
        stime=2,
        rtime=3,
    )
    op_c = Operation(
        symbol="c",
        proc=2,
        type="rd",
        obj=1,
        ival="somekey",
        oval="somevalue",
        stime=4,
        rtime=5,
    )
    # a --vis-> b
    vis = {Relation(sub=op_a, obj=op_b, rel="vis")}

    # b --so-> c
    rb = {Relation(sub=op_b, obj=op_c, rel="rb")}
    ss = {Relation(sub=op_b, obj=op_c, rel="ss")}

    hist = History(
        ops={op_a, op_b, op_c},
        rb=rb,
        ss=ss,
    )

    ae = AbstractExecution(
        hist=hist,
        vis=vis,
    )

    print(MonotonicRead.check(ae))

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
