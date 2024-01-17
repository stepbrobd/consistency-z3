import z3


class Operation:
    _op = None
    _op_type = None
    _op_symbols = None


    @staticmethod
    def Create() -> z3.DatatypeSortRef:
        """
        op = Operation.Create()
        """
        if Operation._op is not None:
            return Operation._op

        OperationType, (_, _) = Operation.Sort()
        Operation._op = z3.Datatype("Operation")
        # nil constructor must not be declared
        # Operation.declare("nil")
        Operation._op.declare("cons",
            ("proc", z3.IntSort()),    # process id
            ("type", OperationType),   # operation type
            ("obj", z3.IntSort()),     # invoking object
            ("ival", z3.StringSort()), # input value
            ("oval", z3.StringSort()), # output value
            ("stime", z3.IntSort()),   # start time
            ("rtime", z3.IntSort())    # return time
        )
        Operation._op = Operation._op.create()

        return Operation._op


    @staticmethod
    def Sort() -> tuple[z3.DatatypeSortRef, tuple[z3.DatatypeRef, ...]]:
        """
        OperationType, (rd, wr) = Operation.Sort()
        """
        if Operation._op_type is not None:
            return Operation._op_type

        Operation._op_type = z3.EnumSort("OperationType", ["rd", "wr"])

        return Operation._op_type


    @staticmethod
    def Const(name: str) -> z3.DatatypeRef:
        """
        x = Operation.Const("x")
        """
        if Operation._op_symbols is None:
            Operation._op_symbols = {}

        if name in Operation._op_symbols:
            return Operation._op_symbols[name]

        op = Operation.Create()
        Operation._op_symbols[name]= z3.Const(name, op)

        return Operation._op_symbols[name]


    @staticmethod
    def Consts(names: str) -> tuple[z3.DatatypeRef, ...]:
        """
        x, y = Operation.Consts("x y")
        """
        return tuple(map(Operation.Const, names.split()))
