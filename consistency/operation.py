import z3


class Operation:
    _op = None
    _op_type = None
    _op_symbols: dict[str, z3.DatatypeRef] | None = None


    @staticmethod
    def Create(extensions: list[tuple[str, z3.SortRef]] | None = None) -> z3.DatatypeSortRef:
        """
        op = Operation.Create()  # default fields only
        op = Operation.Create([("svc", z3.IntSort())])  # with additional fields
        """
        if Operation._op is not None:
            return Operation._op # type: ignore

        OperationType, (_, _) = Operation.Sort()
        Operation._op = z3.Datatype("Operation")

        # always include base declarations
        base = [
            ("proc", z3.IntSort()),  # process id
            ("type", OperationType),  # operation type
            ("obj", z3.IntSort()),  # invoking object
            ("ival", z3.StringSort()),  # input value
            ("oval", z3.StringSort()),  # output value
            ("stime", z3.IntSort()),  # start time
            ("rtime", z3.IntSort()),  # return time
        ]

        if extensions is not None:
            # check extension field names don't conflict with base fields
            base_names = {field[0] for field in base}
            for extension_name, _ in extensions:
                if extension_name in base_names:
                    raise ValueError(f"extension name `{extension_name}` conflicts with base fields")

            all_fields = base + extensions
        else:
            all_fields = base

        Operation._op.declare("cons", *all_fields)
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

        return Operation._op_type  # type: ignore


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
        Operation._op_symbols[name] = z3.Const(name, op)  # type: ignore

        return Operation._op_symbols[name]


    @staticmethod
    def Consts(names: str) -> tuple[z3.DatatypeRef, ...]:
        """
        x, y = Operation.Consts("x y")
        """
        return tuple(map(Operation.Const, names.split()))
