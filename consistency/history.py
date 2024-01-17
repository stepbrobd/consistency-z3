import z3

from consistency.operation import Operation as Op
from consistency.relation import Relation as Rel


class History:
    class Relation(Rel):
        @staticmethod
        def returns_before() -> z3.FuncDeclRef:
            op = Op.Create()
            rb = History.Relation.Declare("rb", op, op, z3.BoolSort())

            a, b = Op.Consts("a b")
            History.Relation.AddConstraint("rb",
                z3.Implies(rb(a, b), op.rtime(a) < op.stime(b))
            )

            return rb


        @staticmethod
        def same_session() -> z3.FuncDeclRef:
            op = Op.Create()
            ss = History.Relation.Declare("ss", op, op, z3.BoolSort())

            a, b = Op.Consts("a b")
            History.Relation.AddConstraint("ss",
                z3.Implies(ss(a, b), op.proc(a) == op.proc(b))
            )

            return ss


        @staticmethod
        def session_order() -> z3.FuncDeclRef:
            op = Op.Create()
            so = History.Relation.Declare("so", op, op, z3.BoolSort())

            a, b = Op.Consts("a b")
            rb = History.Relation.returns_before()
            ss = History.Relation.same_session()
            History.Relation.AddConstraint("so",
                # so is the intersection of rb and ss
                z3.Implies(so(a, b), z3.And(rb(a, b), ss(a, b)))
            )

            return so
