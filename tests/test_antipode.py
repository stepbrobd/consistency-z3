import z3

from consistency.abstract_execution import AbstractExecution as AE
from consistency.common import check, cleanup
from consistency.history import History as H
from consistency.model.model import Model
from consistency.operation import Operation as Op
from consistency.relation import Relation as Rel


class Antipode:
    class Relation(Rel):
        @staticmethod
        def lineage() -> z3.FuncDeclRef:
            hb = AE.Relation.happens_before()
            viewed = AE.Relation.viewed()
            so = H.Relation.session_order()
            ob = H.Relation.same_object()

            op = Op.Create([("svc", z3.IntSort())])
            lineage = Antipode.Relation.Declare("lineage", op, op, z3.BoolSort())

            _, (rd, wr) = Op.Sort()
            a, b, x, y = Op.Consts("a b x y")

            Antipode.Relation.AddConstraint(
                "lineage",
                z3.And(  # type: ignore
                    # 0. DAG: acyclicity and transitivity
                    z3.ForAll(
                        [a, b], z3.Implies(lineage(a, b), z3.Not(lineage(b, a)))
                    ),
                    z3.ForAll(
                        [a, b, x],
                        z3.Implies(
                            z3.And(lineage(a, x), lineage(x, b)), lineage(a, b)
                        ),
                    ),
                    # 1. single root
                    z3.ForAll(
                        [a],
                        z3.Exists(
                            [x],
                            z3.And(
                                lineage(x, a), z3.Not(z3.Exists([y], lineage(y, x)))
                            ),
                        ),
                    ),
                    # 2. strict ordering within same process
                    z3.ForAll(
                        [a, b],
                        z3.Implies(
                            z3.And(
                                so(a, b),
                                op.proc(a) == op.proc(b),  # type: ignore
                            ),
                            lineage(a, b),
                        ),
                    ),
                    # 3. send/receive pairs in same service
                    z3.ForAll(
                        [a, b],
                        z3.Implies(
                            z3.And(
                                hb(a, b),
                                op.svc(a) == op.svc(b),  # type: ignore
                            ),
                            lineage(a, b),
                        ),
                    ),
                    # 4. invocation correspondence between services
                    z3.ForAll(
                        [a, b],
                        z3.Implies(
                            z3.And(
                                ob(a, b),
                                hb(a, b),  # a happens before b
                                op.svc(a) != op.svc(b),  # different services # type: ignore
                            ),
                            lineage(a, b),
                        ),
                    ),
                    # 5. reply correspondence through reads
                    z3.ForAll(
                        [a, b],
                        z3.Implies(
                            z3.And(
                                viewed(b, a),  # b reads value written by a
                                op.svc(a) != op.svc(b),  # different services # type: ignore
                            ),
                            lineage(a, b)
                        )
                    ),
                ),
            )
            return lineage


class XCY(Model):
    @staticmethod
    def assertions() -> z3.BoolRef:  # predicates
        _, (rd, wr) = Op.Sort()
        op = Op.Create([("svc", z3.IntSort())])
        a, b, x = Op.Consts("a b x")

        hb = AE.Relation.happens_before()
        vis = AE.Relation.visibility()
        viewed = AE.Relation.viewed()
        lineage = Antipode.Relation.lineage()
        return z3.And(
            # hb
            z3.ForAll([a, b], z3.Implies(hb(a, b), vis(a, b))),
            # transitivity already implied by hb and lineage
            # read from lineage
            # try 1:
            # reading from a write creates dependencies with its lineage
            # z3.ForAll([a, b, x],
            #     z3.Implies(
            #         z3.And(
            #             viewed(b, a),  # b reads from a
            #             lineage(x, a)   # x is in a's lineage
            #         ),
            #         vis(x, b)  # x must be visible to b
            #     )
            # ),
            # try 2:
            z3.ForAll(
                [a, b],
                z3.Implies(
                    z3.And(
                        viewed(b, a),  # b reads from a
                        op.type(a) == wr,  # type: ignore # a is a write
                        op.type(b) == rd,  # type: ignore # b is a read
                    ),
                    z3.ForAll(
                        [x],
                        z3.Implies(
                            lineage(x, a),  # x is in a's lineage
                            hb(x, b),  # x is ordered before b
                        ),
                    ),
                ),
            ),
        )


@cleanup
def test_antipode() -> None:
    # an execution x is XCY consistent if for each process p_i
    # there is a serialization of the all write and p_i's read
    # events of x that respects happens-before (not exactly)
    assert check(XCY.assertions())
