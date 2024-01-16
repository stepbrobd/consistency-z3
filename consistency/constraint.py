import z3


class Constraint:
    __op__ = None
    __op_type__ = None
    __op_symbols__ = None
    __op_functions__ = None


    @staticmethod
    def declare_operation() -> z3.DatatypeSortRef:
        """
        op = Constraint.declare_operation()
        """
        if Constraint.__op__ is not None:
            return Constraint.__op__
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
        Constraint.__op__ = Operation.create()
        return Constraint.__op__


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
    def declare_operation_symbol(symbol: str) -> z3.DatatypeRef:
        """
        a = Constraint.declare_operation_symbol("a")
        """
        if Constraint.__op_symbols__ is None:
            Constraint.__op_symbols__ = {}
        if symbol in Constraint.__op_symbols__:
            return Constraint.__op_symbols__[symbol]
        op = Constraint.declare_operation()
        ref = z3.Const(symbol, op)
        Constraint.__op_symbols__[symbol] = ref
        return Constraint.__op_symbols__[symbol]


    @staticmethod
    def declare_operation_symbols(symbols: str) -> tuple[z3.DatatypeRef, ...]:
        """
        a, b = Constraint.declare_operation_symbols("a b")
        """
        return tuple(map(Constraint.declare_operation_symbol, symbols.split()))


    @staticmethod
    def declare_operation_function(name: str, *sig: z3.SortRef) -> z3.FuncDeclRef:
        """
        f = Constraint.declare_operation_function("f", z3.IntSort(), z3.IntSort())
        """
        if Constraint.__op_functions__ is None:
            Constraint.__op_functions__ = {}
        if name in Constraint.__op_functions__:
            return Constraint.__op_functions__[name]
        Constraint.__op_functions__[name] = z3.Function(name, *sig)
        return Constraint.__op_functions__[name]


    @staticmethod
    def returns_before(s: z3.Solver) -> z3.FuncDeclRef:
        op = Constraint.declare_operation()
        a, b = Constraint.declare_operation_symbols("a b")
        rb = Constraint.declare_operation_function("rb", op, op, z3.BoolSort())
        s.add(z3.ForAll([a, b],
            z3.Implies(rb(a, b), op.rtime(a) < op.stime(b))
        ))
        return rb


    @staticmethod
    def same_session(s: z3.Solver) -> z3.FuncDeclRef:
        op = Constraint.declare_operation()
        a, b = Constraint.declare_operation_symbols("a b")
        ss = Constraint.declare_operation_function("ss", op, op, z3.BoolSort())
        s.add(z3.ForAll([a, b],
            z3.Implies(ss(a, b), op.proc(a) == op.proc(b))
        ))
        return ss


    @staticmethod
    def session_order(s: z3.Solver) -> z3.FuncDeclRef:
        op = Constraint.declare_operation()
        a, b = Constraint.declare_operation_symbols("a b")
        rb = Constraint.returns_before(s)
        ss = Constraint.same_session(s)
        so = Constraint.declare_operation_function("so", op, op, z3.BoolSort())
        s.add(z3.ForAll([a, b],
            z3.Implies(so(a, b), z3.And(rb(a, b), ss(a, b)))
        ))
        return so


    @staticmethod
    def visibility(s: z3.Solver) -> z3.FuncDeclRef:
        _, (rd, wr) = Constraint.declare_operation_type()
        op = Constraint.declare_operation()
        a, b, c = Constraint.declare_operation_symbols("a b c")
        vis = Constraint.declare_operation_function("vis", op, op, z3.BoolSort())
        s.add(z3.And(
            # op a's effect is visible to op b
            z3.ForAll([a, b],
                z3.Implies(
                    vis(a, b),
                    z3.And(op.type(a) == wr, op.type(b) == rd, op.obj(a) == op.obj(b), op.rtime(a) < op.stime(b))
                )
            ),
            # acyclicity
            z3.ForAll([a, b], z3.Implies(vis(a, b), z3.Not(vis(b, a)))),
            # transitivity
            z3.ForAll([a, b, c], z3.Implies(z3.And(vis(a, b), vis(b, c)), vis(a, c))),
        ))
        return vis


    @staticmethod
    def arbitration(s: z3.Solver) -> z3.FuncDeclRef:
        op = Constraint.declare_operation()
        a, b, c = Constraint.declare_operation_symbols("a b c")
        ar = Constraint.declare_operation_function("ar", op, op, z3.BoolSort())
        s.add(z3.And(
            # ordering
            z3.ForAll([a, b],
                z3.Implies(ar(a, b), op.rtime(a) < op.stime(b))
            ),
            # acyclicity
            z3.ForAll([a, b], z3.Implies(ar(a, b), z3.Not(ar(b, a)))),
            # transitivity
            z3.ForAll([a, b, c], z3.Implies(z3.And(ar(a, b), ar(b, c)), ar(a, c))),
        ))
        return ar
