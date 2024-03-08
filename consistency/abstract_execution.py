import z3

from consistency.history import History as H
from consistency.operation import Operation as Op
from consistency.relation import Relation as Rel


class AbstractExecution:
    class Relation(Rel):
        @staticmethod
        def visibility() -> z3.FuncDeclRef:
            op = Op.Create()
            vis = AbstractExecution.Relation.Declare("vis", op, op, z3.BoolSort())

            _, (rd, wr) = Op.Sort()
            a, b, c = Op.Consts("a b c")
            AbstractExecution.Relation.AddConstraint("vis",
                z3.And(
                    # op a's effect is visible to op b
                    z3.If(z3.And(op.type(a) == wr, op.type(b) == rd),
                        z3.Implies(
                            vis(a, b),
                            z3.And(op.obj(a) == op.obj(b), op.rtime(a) < op.stime(b))
                        ),
                        z3.BoolVal(True)
                    ),
                    # acyclicity
                    z3.ForAll([a, b], z3.Implies(vis(a, b), z3.Not(vis(b, a)))),
                    # transitivity
                    z3.ForAll([a, b, c], z3.Implies(z3.And(vis(a, b), vis(b, c)), vis(a, c))),
                )
            )

            return vis


        @staticmethod
        def arbitration() -> z3.FuncDeclRef:
            op = Op.Create()
            ar = AbstractExecution.Relation.Declare("ar", op, op, z3.BoolSort())

            a, b, c = Op.Consts("a b c")
            AbstractExecution.Relation.AddConstraint("ar",
                z3.And(
                    # ordering
                    z3.Implies(ar(a, b), op.rtime(a) < op.stime(b)),
                    # acyclicity
                    z3.ForAll([a, b], z3.Implies(ar(a, b), z3.Not(ar(b, a)))),
                    # transitivity
                    z3.ForAll([a, b, c], z3.Implies(z3.And(ar(a, b), ar(b, c)), ar(a, c))),
                )
            )

            return ar


        @staticmethod
        def happens_before() -> z3.FuncDeclRef:
            op = Op.Create()
            hb = AbstractExecution.Relation.Declare("hb", op, op, z3.BoolSort())

            a, b = Op.Consts("a b")
            H.Relation.session_order()
            AbstractExecution.Relation.visibility()

            AbstractExecution.Relation.AddConstraint("hb",
                z3.And(
                    # hb is the transitive closure of the union of so and vis
                )
            )

            return hb
