import z3

from consistency.history import History as H
from consistency.operation import Operation as Op
from consistency.relation import Relation as Rel


class AbstractExecution:
    class Relation(Rel):
        @staticmethod
        def viewed() -> z3.FuncDeclRef:
            op = Op.Create()
            viewed = AbstractExecution.Relation.Declare("viewed", op, op, z3.BoolSort())

            _, (rd, wr) = Op.Sort()
            a, b, c = Op.Consts("a b c")
            vis = AbstractExecution.Relation.visibility()
            AbstractExecution.Relation.AddConstraint("viewed", z3.And( # type: ignore
                # write-read: if b has seen a, subsequent reads after b must see data as up-to-date as a
                # this also applies to concurrent writes
                z3.If(z3.And(op.type(a) == wr, op.type(b) == rd, op.obj(a) == op.obj(b)), z3.Implies(viewed(a, b), # type: ignore
                    z3.If(z3.Or(
                        # non-concurrent
                        op.rtime(a) < op.stime(b), # type: ignore
                        # concurrent
                        # this only captures the case where a and b *MIGHT* be concurrent
                        # all of the below 4 are considered as the constraints for CAN VIEW
                        z3.And(op.stime(a) <= op.stime(b), op.rtime(a) >= op.rtime(a)), # type: ignore
                        z3.And(op.stime(a) >= op.stime(b), op.rtime(a) <= op.rtime(b)), # type: ignore
                        z3.And(op.stime(b) <= op.rtime(a), op.rtime(a) <= op.rtime(b)), # type: ignore
                        z3.And(op.stime(b) <= op.stime(a), op.stime(a) <= op.rtime(b)), # type: ignore
                    ),
                    # then
                    vis(a, b), # FIXME
                    # else
                    z3.BoolVal(True)
                )), z3.BoolVal(True)),
                # read-read: b's value being returned must track the closest write that's visible to a
                # c -> ... -> a -> b
                # wr...rd...rd...rd
                z3.If(z3.And(op.type(a) == rd, op.type(b) == rd, op.obj(a) == op.obj(b)), z3.Implies(viewed(a, b), # type: ignore
                    z3.Exists([c], z3.And(
                        op.type(c) == wr, # type: ignore
                        vis(c, a), # FIXME: should be can view
                        op.ival(c) == op.oval(a), op.ival(c) == op.oval(b), op.obj(b) == op.obj(a), # type: ignore
                    ))
                ), z3.BoolVal(True)),
                # acyclicity
                z3.ForAll([a, b], z3.Implies(viewed(a, b), z3.Not(viewed(b, a)))),
                # transitivity
                z3.ForAll([a, b, c], z3.Implies(z3.And(viewed(a, b), viewed(b, c)), viewed(a, c))),
            ))

            return viewed


        @staticmethod
        def visibility() -> z3.FuncDeclRef:
            op = Op.Create()
            vis = AbstractExecution.Relation.Declare("vis", op, op, z3.BoolSort())

            _, (rd, wr) = Op.Sort()
            a, b, c = Op.Consts("a b c")
            AbstractExecution.Relation.AddConstraint("vis",
                z3.And( # type: ignore
                    # op a's effect is visible to op b
                    z3.If(z3.And(op.type(a) == wr, op.type(b) == rd), # type: ignore
                        z3.Implies(vis(a, b),
                            z3.And( # definitive encoding, if this condition is met, a must be visible to b
                                op.obj(a) == op.obj(b),    # type: ignore
                                op.rtime(a) < op.stime(b), # type: ignore
                            )
                            # capture the ambiguity due to concurrent operations
                            # but not needed as the monotonic read will include the new "viewed" partial order
                            # z3.And(op.obj(a) == op.obj(b), z3.Or(
                            #     # non-concurrent
                            #     op.rtime(a) < op.stime(b),
                            #     # concurrent
                            #     # this only captures the case where a and b *MIGHT* be concurrent
                            #     z3.And(op.stime(a) <= op.stime(b), op.rtime(a) >= op.rtime(a)),
                            #     z3.And(op.stime(a) >= op.stime(b), op.rtime(a) <= op.rtime(b)),
                            #     z3.And(op.stime(b) <= op.rtime(a), op.rtime(a) <= op.rtime(b)),
                            #     z3.And(op.stime(b) <= op.stime(a), op.stime(a) <= op.rtime(b)),
                            # ))
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
                z3.And( # type: ignore
                    # ordering
                    z3.Implies(ar(a, b), op.rtime(a) < op.stime(b)), # type: ignore
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
                z3.And( # type: ignore
                    # hb is the transitive closure of the union of so and vis
                )
            )

            return hb
