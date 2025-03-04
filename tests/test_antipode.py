import z3

from consistency.abstract_execution import AbstractExecution as AE
from consistency.common import check, cleanup, compatible
from consistency.history import History as H
from consistency.model.causal_consistency import CausalConsistency
from consistency.model.model import Model
from consistency.operation import Operation as Op
from consistency.relation import Relation as Rel

op = Op.Create(
    [
        ("svc", z3.IntSort()),
        ("is_init", z3.BoolSort()),
        ("is_exit", z3.BoolSort()),
        ("is_send", z3.BoolSort()),
        ("is_recv", z3.BoolSort()),
        ("is_invoke", z3.BoolSort()),
        ("is_reply", z3.BoolSort()),
    ]
)


class Antipode:
    class Relation(Rel):
        @staticmethod
        def lineage() -> z3.FuncDeclRef:
            op = Op.Create(
                [
                    ("svc", z3.IntSort()),
                    ("is_init", z3.BoolSort()),
                    ("is_exit", z3.BoolSort()),
                    ("is_send", z3.BoolSort()),
                    ("is_recv", z3.BoolSort()),
                    ("is_invoke", z3.BoolSort()),
                    ("is_reply", z3.BoolSort()),
                ]
            )
            lineage = Antipode.Relation.Declare("lineage", op, op, z3.BoolSort())
            hb = AE.Relation.happens_before()
            so = H.Relation.session_order()
            a, b, x, y, m, n = Op.Consts("a b x y m n")
            Antipode.Relation.AddConstraint(
                "lineage",
                z3.And(  # type: ignore
                    # base cases
                    # init can be exit and vice versa, no constraint here
                    # no constraint for local ops
                    # existential quantification for send/recv pairs
                    z3.If(
                        z3.And(
                            op.is_send(m),  # type: ignore
                            op.is_recv(n),  # type: ignore
                        ),
                        z3.And(
                            op.proc(m) != op.proc(n),  # type: ignore
                            op.svc(m) == op.svc(n),  # type: ignore
                        ),
                        z3.BoolVal(True),
                    ),
                    # existential quantification for invoke/reply pairs
                    z3.If(
                        z3.And(
                            op.is_invoke(m),  # type: ignore
                            op.is_reply(n),  # type: ignore
                        ),
                        op.svc(m) != op.svc(n),  # type: ignore
                        z3.BoolVal(True),
                    ),
                    # 0. transitivity
                    z3.ForAll(
                        [a, b, x],
                        z3.Implies(z3.And(lineage(a, x), lineage(x, b)), lineage(a, b)),
                    ),
                    # 1. single root (init)
                    z3.ForAll(
                        [a],
                        z3.Implies(
                            z3.Not(op.is_init(a)),  # type: ignore
                            z3.Exists(
                                [x],
                                z3.And(
                                    op.is_init(x),  # type: ignore
                                    lineage(x, a),
                                    z3.Not(z3.Exists([y], lineage(y, x))),
                                ),
                            ),
                        ),
                    ),
                    # 2. strict ordering within same process (non exit ops)
                    z3.ForAll(
                        [a, b],
                        z3.Implies(
                            z3.And(
                                so(a, b),
                                z3.Not(op.is_exit(a)),  # type: ignore
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
                                op.is_send(a),  # type: ignore
                                op.is_recv(b),  # type: ignore
                                op.svc(a) == op.svc(b),  # type: ignore
                                hb(a, b),
                            ),
                            lineage(a, b),
                        ),
                    ),
                    # 4. invocation correspondence between service
                    z3.ForAll(
                        [a, b],
                        z3.Implies(
                            z3.And(
                                op.is_invoke(a),  # type: ignore
                                op.svc(a) != op.svc(b),  # type: ignore
                                hb(a, b),
                            ),
                            lineage(a, b),
                        ),
                    ),
                    # 5. reply correspondence through reads
                    z3.ForAll(
                        [a, b],
                        z3.Implies(
                            z3.And(
                                op.is_reply(a),  # type: ignore
                                hb(a, b),
                            ),
                            lineage(a, b),
                        ),
                    ),
                ),
            )
            return lineage


class XCY(Model):
    @staticmethod
    def assertions() -> z3.BoolRef:  # predicates
        _, (rd, wr) = Op.Sort()
        op = Op.Create(
            [
                ("svc", z3.IntSort()),
                ("is_init", z3.BoolSort()),
                ("is_exit", z3.BoolSort()),
                ("is_send", z3.BoolSort()),
                ("is_recv", z3.BoolSort()),
                ("is_invoke", z3.BoolSort()),
                ("is_reply", z3.BoolSort()),
            ]
        )
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
    assert compatible(XCY.assertions(), CausalConsistency.assertions())
    assert check(XCY.assertions())
