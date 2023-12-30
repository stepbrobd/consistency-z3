from typing import Self

import z3


class Context:
    def __init__(self: Self) -> None:
        self.ctx = z3.Context()

        self.op_type, (self.rd, self.wr) = z3.EnumSort("OperationType", ["rd", "wr"], ctx=self.ctx)

        self.op = z3.Datatype("Operation", self.ctx)
        self.op.declare("cons",
            ("proc", z3.IntSort(ctx=self.ctx)),    # process id
            ("type", self.op_type),                # operation type
            ("obj", z3.IntSort(ctx=self.ctx)),     # invoking object
            ("ival", z3.StringSort(ctx=self.ctx)), # input value
            ("oval", z3.StringSort(ctx=self.ctx)), # output value
            ("stime", z3.IntSort(ctx=self.ctx)),   # start time
            ("rtime", z3.IntSort(ctx=self.ctx)),   # return time
        )
        self.op = self.op.create()

        self.rb = z3.Function("rb", self.op, self.op, z3.BoolSort(), ctx=self.ctx)
        self.ss = z3.Function("ss", self.op, self.op, z3.BoolSort(), ctx=self.ctx)
        self.so = z3.Function("so", self.op, self.op, z3.BoolSort(), ctx=self.ctx)
        self.vis = z3.Function("vis", self.op, self.op, z3.BoolSort(), ctx=self.ctx)
