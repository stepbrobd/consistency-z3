import z3

from consistency.history import History
from consistency.operation import Operation as Op
from consistency.relation import Relation as Rel


class AbstractExecution:
    class Relation(Rel):
        @staticmethod
        def can_view() -> z3.FuncDeclRef:
            # can_view(a, b) -> a (rd) can view b (wr)
            op = Op.Create()
            can_view = AbstractExecution.Relation.Declare(
                "can_view", op, op, z3.BoolSort()
            )

            _, (rd, wr) = Op.Sort()
            a, b = Op.Consts("a b")
            AbstractExecution.Relation.AddConstraint(
                "can_view",
                z3.Implies(
                    can_view(a, b),
                    z3.If(
                        # conditions: write-read pair invoked on the same object
                        z3.And(
                            op.type(a) == rd,  # type: ignore
                            op.type(b) == wr,  # type: ignore
                            op.obj(a) == op.obj(b),  # type: ignore
                        ),
                        # then
                        z3.And(
                            # allow atomic ops
                            op.rtime(a) >= op.stime(a),  # type: ignore
                            op.rtime(b) >= op.stime(b),  # type: ignore
                            # timing constraints
                            z3.Or(
                                # non-concurrent
                                op.stime(a) > op.rtime(b),  # type: ignore
                                # concurrent
                                # this only captures the case where a and b *MIGHT* be concurrent
                                z3.And(op.stime(a) <= op.stime(b), op.stime(a) <= op.rtime(b), op.rtime(a) >= op.stime(b), op.rtime(a) >= op.rtime(b)), # type: ignore
                                z3.And(op.stime(a) >= op.stime(b), op.stime(a) <= op.rtime(b), op.rtime(a) >= op.stime(b), op.rtime(a) >= op.rtime(b)), # type: ignore
                                z3.And(op.stime(a) <= op.stime(b), op.stime(a) <= op.rtime(b), op.rtime(a) >= op.stime(b), op.rtime(a) <= op.rtime(b)), # type: ignore
                                z3.And(op.stime(a) >= op.stime(b), op.stime(a) <= op.rtime(b), op.rtime(a) >= op.stime(b), op.rtime(a) <= op.rtime(b)), # type: ignore
                            ),
                        ),
                        # else
                        z3.BoolVal(True),
                    ),
                ),
            )

            return can_view


        @staticmethod
        def viewed() -> z3.FuncDeclRef:
            # viewed(a, b) -> a (rd) viewed b (wr)
            op = Op.Create()
            viewed = AbstractExecution.Relation.Declare("viewed", op, op, z3.BoolSort())
            can_view = AbstractExecution.Relation.can_view()

            _, (rd, wr) = Op.Sort()
            a, b, x = Op.Consts("a b x")
            AbstractExecution.Relation.AddConstraint(
                "viewed",
                z3.Implies(
                    viewed(a, b),
                    z3.And(
                        can_view(a, b),
                        z3.Or(
                            # b -vis-> a
                            # x -vis-> a
                            # where x concur b
                            # strict value equavalence
                            op.oval(a) == op.ival(b), # type: ignore
                            # there might be a write that happened after the write b or concurrent to write b
                            # that changes the value of read a (still legal)
                            # need to ensure the output of read a is either the value of write b or the value of a write x that happened
                            z3.Exists(
                                x,
                                z3.And(
                                    op.type(x) == wr, # type: ignore
                                    # make sure x is after write b or concurrent to write b
                                    # allow atomic ops
                                    op.rtime(x) >= op.stime(x),  # type: ignore
                                    op.rtime(b) >= op.stime(b),  # type: ignore
                                    # timing constraints
                                    z3.Or(
                                        # non-concurrent
                                        op.stime(x) > op.rtime(b),  # type: ignore
                                        # concurrent
                                        z3.And(op.stime(x) <= op.stime(b), op.stime(x) <= op.rtime(b), op.rtime(x) >= op.stime(b), op.rtime(x) >= op.rtime(b)), # type: ignore
                                        z3.And(op.stime(x) >= op.stime(b), op.stime(x) <= op.rtime(b), op.rtime(x) >= op.stime(b), op.rtime(x) >= op.rtime(b)), # type: ignore
                                        z3.And(op.stime(x) <= op.stime(b), op.stime(x) <= op.rtime(b), op.rtime(x) >= op.stime(b), op.rtime(x) <= op.rtime(b)), # type: ignore
                                        z3.And(op.stime(x) >= op.stime(b), op.stime(x) <= op.rtime(b), op.rtime(x) >= op.stime(b), op.rtime(x) <= op.rtime(b)), # type: ignore
                                    ),
                                    op.oval(a) == op.ival(x), # type: ignore
                                ),
                            ),
                        ),
                    ),
                ),
            )

            return viewed


        @staticmethod
        def visibility() -> z3.FuncDeclRef:
            op = Op.Create()
            vis = AbstractExecution.Relation.Declare("vis", op, op, z3.BoolSort())
            ar = AbstractExecution.Relation.arbitration()
            viewed = AbstractExecution.Relation.viewed()

            _, (rd, wr) = Op.Sort()
            a, b, c, x = Op.Consts("a b c x")
            AbstractExecution.Relation.AddConstraint(
                "vis",
                z3.And( # type: ignore
                    # case analysis on op type
                    # i think 4 explicit z3.If statements can work here but it's not clear
                    # that only 1 of them can be true at a time, so i'm using z3.Or
                    z3.Or(
                        # case 1: read-read pair
                        # previous read needs to track to its closest visible write if any
                        # and propagate the write to the later read
                        z3.If( # type: ignore
                            z3.And(op.type(a) == rd, op.type(b) == rd), # type: ignore
                            z3.Implies(
                                z3.Exists(
                                    x,
                                    z3.And(
                                        op.type(x) == wr, # type: ignore
                                        vis(x, a),
                                    ),
                                ),
                                vis(x, b), # thought about changing this to ar(x, b)
                                # but vis(x, b) is more relaxed
                            ),
                            z3.BoolVal(True),
                        ),
                        # case 2: read-write pair
                        # undefined
                        z3.If( # type: ignore
                            z3.And(op.type(a) == rd, op.type(b) == wr), # type: ignore
                            z3.BoolVal(True),
                            z3.BoolVal(True),
                        ),
                        # case 3: write-read pair
                        # equivalent to viewed + arbitration
                        # i.e. make sure the write and read have a linearization point
                        z3.If( # type: ignore
                            z3.And(op.type(a) == wr, op.type(b) == rd), # type: ignore
                            z3.Implies(viewed(b, a), ar(b, a)),
                            z3.BoolVal(True),
                        ),
                        # case 4: write-write pair
                        # undefined
                        z3.If( # type: ignore
                            z3.And(op.type(a) == wr, op.type(b) == wr), # type: ignore
                            z3.BoolVal(True),
                            z3.BoolVal(True),
                        ),
                    ),
                    # acyclicity
                    z3.ForAll([a, b], z3.Implies(vis(a, b), z3.Not(vis(b, a)))),
                    # transitivity
                    z3.ForAll(
                        [a, b, c], z3.Implies(z3.And(vis(a, b), vis(b, c)), vis(a, c))
                    ),
                ),
            )

            return vis


        @staticmethod
        def arbitration() -> z3.FuncDeclRef:
            op = Op.Create()
            ar = AbstractExecution.Relation.Declare("ar", op, op, z3.BoolSort())

            a, b, c = Op.Consts("a b c")
            AbstractExecution.Relation.AddConstraint(
                "ar",
                z3.And(  # type: ignore
                    # ordering
                    z3.Implies(ar(a, b), op.rtime(a) < op.stime(b)),  # type: ignore
                    # acyclicity
                    z3.ForAll([a, b], z3.Implies(ar(a, b), z3.Not(ar(b, a)))),
                    # transitivity
                    z3.ForAll(
                        [a, b, c], z3.Implies(z3.And(ar(a, b), ar(b, c)), ar(a, c))
                    ),
                ),
            )

            return ar


        @staticmethod
        def happens_before() -> z3.FuncDeclRef:
            op = Op.Create()
            hb = AbstractExecution.Relation.Declare("hb", op, op, z3.BoolSort())
            so = History.Relation.session_order()
            vis = AbstractExecution.Relation.visibility()

            a, b = Op.Consts("a b")
            AbstractExecution.Relation.AddConstraint(
                "hb",
                z3.And(  # type: ignore
                    # transitive closure
                    # hb is the transitive closure of the union of so and vis
                    # https://theory.stanford.edu/~nikolaj/programmingz3.html#sec-transitive-closure
                    z3.ForAll(
                        [a, b],
                        hb(a, b)
                        == z3.Or(
                            z3.TransitiveClosure(so)(a, b),
                            z3.TransitiveClosure(vis)(a, b),
                        ),
                    ),
                    # acyclicity
                    z3.ForAll([a, b], z3.Implies(hb(a, b), z3.Not(hb(b, a)))),
                ),
            )

            return hb
