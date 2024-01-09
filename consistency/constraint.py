import z3


class Constraint:
    __op_type__ = None

    @staticmethod
    def declare_operation() -> z3.DatatypeSortRef:
        """
        op = Constraint.declare_operation()
        """
        OperationType, (_, _) = Constraint.declare_operation_type()
        Operation = z3.Datatype("Operation")
        Operation.declare("nil")
        Operation.declare("cons",
            ("proc", z3.IntSort()),    # process id
            ("type", OperationType),   # operation type
            ("obj", z3.IntSort()),     # invoking object
            ("ival", z3.StringSort()), # input value
            ("oval", z3.StringSort()), # output value
            ("stime", z3.IntSort()),   # start time
            ("rtime", z3.IntSort())    # return time
        )
        return Operation.create()


    @staticmethod
    def declare_operation_type() -> tuple[z3.DatatypeSortRef, tuple[z3.DatatypeRef, ...]]:
        """
        op_type, (rd, wr) = Constraint.declare_operation_type()
        """
        if Constraint.__op_type__ is not None:
            return Constraint.__op_type__
        Constraint.__op_type__ = z3.EnumSort("OperationType", ["rd", "wr"])
        return Constraint.__op_type__


    @staticmethod
    def returns_before(s: z3.Solver) -> z3.FuncDeclRef:
        op = Constraint.declare_operation()
        a, b = z3.Consts("a b", op)
        rb = z3.Function("rb", op, op, z3.BoolSort())
        s.add(z3.ForAll([a, b],
            z3.Implies(rb(a, b), op.rtime(a) < op.stime(b))
        ))
        return rb


    @staticmethod
    def same_session(s: z3.Solver) -> z3.FuncDeclRef:
        op = Constraint.declare_operation()
        a, b = z3.Consts("a b", op)
        ss = z3.Function("ss", op, op, z3.BoolSort())
        s.add(z3.ForAll([a, b],
            z3.Implies(ss(a, b), op.proc(a) == op.proc(b))
        ))
        return ss


    @staticmethod
    def session_order(s: z3.Solver) -> z3.FuncDeclRef:
        op = Constraint.declare_operation()
        a, b = z3.Consts("a b", op)
        rb = Constraint.returns_before(s)
        ss = Constraint.same_session(s)
        so = z3.Function("so", op, op, z3.BoolSort())
        s.add(z3.ForAll([a, b],
            z3.Implies(so(a, b), z3.And(rb(a, b), ss(a, b)))
        ))
        return so


    @staticmethod
    def visibility(s: z3.Solver) -> z3.FuncDeclRef:
        _, (rd, wr) = Constraint.declare_operation_type()
        op = Constraint.declare_operation()
        a, b, c = z3.Consts("a b c", op)
        vis = z3.Function("vis", op, op, z3.BoolSort())
        # op a's effect is visible to op b
        s.add(z3.ForAll([a, b],
            z3.Implies(
                vis(a, b),
                z3.And(op.type(a) == wr, op.type(b) == rd, op.obj(a) == op.obj(b), op.rtime(a) < op.stime(b))
            )
        ))
        # acyclicity
        s.add(z3.ForAll([a, b], z3.Implies(vis(a, b), z3.Not(vis(b, a)))))
        # transitivity
        s.add(z3.ForAll([a, b, c], z3.Implies(z3.And(vis(a, b), vis(b, c)), vis(a, c))))
        return vis


    @staticmethod
    def arbitration(s: z3.Solver) -> z3.FuncDeclRef:
        op = Constraint.declare_operation()
        a, b, c = z3.Consts("a b c", op)
        ar = z3.Function("ar", op, op, z3.BoolSort())
        # ordering
        s.add(z3.ForAll([a, b],
            z3.Implies(ar(a, b), op.rtime(a) < op.stime(b))
        ))
        # acyclicity
        s.add(z3.ForAll([a, b], z3.Implies(ar(a, b), z3.Not(ar(b, a)))))
        # transitivity
        s.add(z3.ForAll([a, b, c], z3.Implies(z3.And(ar(a, b), ar(b, c)), ar(a, c))))
        return ar
