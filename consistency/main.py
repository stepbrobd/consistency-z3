import z3

from consistency.model.monotonic_read import MonotonicRead


def main() -> int:
    s = z3.Solver()

    op = z3.Datatype("op")
    op.declare("op",
        ("proc", z3.IntSort()),    # process id
        ("type", z3.StringSort()), # operation type
        ("obj", z3.IntSort()),     # invoking object
        ("ival", z3.StringSort()), # input value
        ("oval", z3.StringSort()), # output value
        ("stime", z3.IntSort()),   # start time
        ("rtime", z3.IntSort())    # return time
    )
    op = op.create()

    MonotonicRead.constraints(s, op)

    match s.check():
        case z3.sat:
            print("sat")
            print(s.model())
        case z3.unknown:
            print("unknown")
        case z3.unsat:
            print("unsat")
            print(s.unsat_core())

    # op_a = Operation(
    #     symbol="a",
    #     proc=1,
    #     type="wr",
    #     obj=1,
    #     ival=("somekey", "someval"),
    #     oval=None,
    #     stime=0,
    #     rtime=1,
    # )
    # op_b = Operation(
    #     symbol="b",
    #     proc=2,
    #     type="rd",
    #     obj=1,
    #     ival="somekey",
    #     oval="someval",
    #     stime=2,
    #     rtime=3,
    # )
    # op_c = Operation(
    #     symbol="c",
    #     proc=2,
    #     type="rd",
    #     obj=1,
    #     ival="somekey",
    #     oval="someval",
    #     stime=4,
    #     rtime=5,
    # )
    # # a --vis-> b
    # vis = {Relation(sub=op_a, obj=op_b)}

    # # b --so-> c
    # rb = {Relation(sub=op_b, obj=op_c)}
    # ss = {Relation(sub=op_b, obj=op_c)}

    # hist = History(
    #     ops={op_a, op_b, op_c},
    #     rb=rb,
    #     ss=ss,
    # )

    # ae = AbstractExecution(
    #     hist=hist,
    #     vis=vis,
    # )

    # print(MonotonicRead.check(ae))

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
