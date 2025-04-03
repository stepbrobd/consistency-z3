import z3

from consistency.operation import Operation as Op
from consistency.relation import Relation as Rel


class History:
    class Relation(Rel):
        @staticmethod
        def returns_before(symbols: list[str] | None = None) -> z3.FuncDeclRef:
            if symbols is None:
                symbols = ["a", "b"]
            decl = " ".join(symbols)

            op = Op.Create()
            rb = History.Relation.Declare("rb", op, op, z3.BoolSort())

            a, b, *_ = Op.Consts(decl)
            History.Relation.AddConstraint("rb",
                z3.Implies(rb(a, b), op.rtime(a) < op.stime(b)) # type: ignore
            )

            return rb


        @staticmethod
        def same_session(symbols: list[str] | None = None) -> z3.FuncDeclRef:
            if symbols is None:
                symbols = ["a", "b"]
            decl = " ".join(symbols)

            op = Op.Create()
            ss = History.Relation.Declare("ss", op, op, z3.BoolSort())

            a, b, *_ = Op.Consts(decl)
            History.Relation.AddConstraint("ss",
                z3.Implies(ss(a, b), op.proc(a) == op.proc(b)) # type: ignore
            )
            # each op is in the same session with itself
            History.Relation.AddConstraint("ss", ss(a, a)) # type: ignore
            History.Relation.AddConstraint("ss", ss(b, b)) # type: ignore

            return ss


        @staticmethod
        def session_order(symbols: list[str] | None = None) -> z3.FuncDeclRef:
            if symbols is None:
                symbols = ["a", "b"]
            decl = " ".join(symbols)

            op = Op.Create()
            so = History.Relation.Declare("so", op, op, z3.BoolSort())

            a, b, *_ = Op.Consts(decl)
            rb = History.Relation.returns_before()
            ss = History.Relation.same_session()
            History.Relation.AddConstraint("so",
                # so is the intersection of rb and ss
               z3.Implies(so(a, b), z3.And(rb(a, b), ss(a, b))) # type: ignore
            )

            return so


        @staticmethod
        def same_object(symbols: list[str] | None = None) -> z3.FuncDeclRef:
            if symbols is None:
                symbols = ["a", "b"]
            decl = " ".join(symbols)

            op = Op.Create()
            ob = History.Relation.Declare("ob", op, op, z3.BoolSort())

            a, b, *_ = Op.Consts(decl)
            History.Relation.AddConstraint("ob",
               z3.Implies(ob(a, b), op.obj(a) == op.obj(b)) # type: ignore
            )

            return ob
