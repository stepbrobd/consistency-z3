import z3


class Relation:
    _constraints = None
    _functions = None


    @staticmethod
    def AddConstraint(parent_func: str, constraints: z3.AstVector) -> None:
        """
        Relation.AddConstraint("f", f(x) == 0, f(y) == 1)
        """
        if Relation._constraints is None:
            Relation._constraints = {}

        Relation._constraints[parent_func] = constraints


    @staticmethod
    def Constraints() -> z3.AstVector:
        """
        c = Relation.Constraints()
        """
        vec = z3.AstVector()

        if Relation._constraints is not None:
            for func in Relation._functions.keys():
                vec.push(Relation._constraints[func])

        return vec


    @staticmethod
    def Declare(name: str, *sig: z3.SortRef) -> z3.FuncDeclRef:
        """
        f = Relation.Declare("f", z3.IntSort(), z3.IntSort())
        """
        if Relation._functions is None:
            Relation._functions = {}

        if name in Relation._functions:
            return Relation._functions[name]

        Relation._functions[name] = z3.Function(name, *sig)

        return Relation._functions[name]


    @staticmethod
    def Reset() -> None:
        """
        Relation.Reset()
        """
        Relation._constraints = None
        Relation._functions = None
