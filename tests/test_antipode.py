import z3

from consistency.abstract_execution import AbstractExecution as AE
from consistency.common import cleanup, compatible
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

        @staticmethod
        def xcy() -> z3.FuncDeclRef:
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
            xcy = Antipode.Relation.Declare("xcy", op, op, z3.BoolSort())
            lineage = Antipode.Relation.lineage()
            hb = AE.Relation.happens_before()
            viewed = AE.Relation.viewed()
            a, b, c, x = Op.Consts("a b c x")
            Antipode.Relation.AddConstraint(
                "xcy",
                z3.And(  # type: ignore
                    # 1. happened-before
                    z3.ForAll([a, b], z3.Implies(hb(a, b), xcy(a, b))),
                    # 2. reads-from-lineage
                    z3.ForAll(
                        [x, b],  # x denotes a'
                        z3.Implies(
                            z3.And(
                                op.type(x) == wr,  # type: ignore # a' is a write
                                op.type(b) == rd,  # type: ignore # b  is a read
                                viewed(b, x),  # b returns value written by a'
                            ),
                            z3.And(
                                xcy(a, b),
                                z3.ForAll([a], lineage(a, x)),  # a in a's lineage
                            ),
                        ),
                    ),
                    # 3. transitivity
                    z3.ForAll(
                        [a, b, c], z3.Implies(z3.And(xcy(a, b), xcy(b, c)), xcy(a, c))
                    ),
                ),
            )
            return xcy


class XCY(Model):
    @staticmethod
    def existential() -> z3.BoolRef:
        # an execution x is XCY consistent if for each process p_i
        # there is a serialization of the all write and p_i's read
        # events of x that respects xcy relation
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
        read, write = Op.Consts("read write")
        xcy = Antipode.Relation.xcy()
        return z3.And(
            op.type(read) == rd,  # type: ignore
            op.type(write) == wr,  # type: ignore
            z3.Exists(
                [write],
                z3.And(
                    op.proc(read) == op.proc(write),  # type: ignore
                    z3.ForAll([read], xcy(write, read)),
                ),
            ),
        )

    @staticmethod
    def assertions() -> z3.BoolRef:
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
        a, b, p = Op.Consts("a b p")
        xcy = Antipode.Relation.xcy()
        so = H.Relation.session_order()
        # for each process p, all reads and writes respect XCY order
        return z3.ForAll(
            [p],  # for each process
            z3.ForAll(
                [a, b],  # for all op a and b
                z3.Implies(
                    z3.And(
                        a != b,
                        z3.Or(
                            # a is read in process p
                            z3.And(
                                op.type(a) == rd,  # type: ignore
                                op.proc(a) == op.proc(p),  # type: ignore
                            ),
                            # a is any write
                            op.type(a) == wr,  # type: ignore
                        ),
                        z3.Or(
                            # b is read in process p
                            z3.And(
                                op.type(b) == rd,  # type: ignore
                                op.proc(b) == op.proc(p),  # type: ignore
                            ),
                            # b is any write
                            op.type(b) == wr,  # type: ignore
                        ),
                        z3.If(
                            # write a and read b in have some serialization
                            z3.And(op.type(a) == wr, op.type(b) == rd),  # type: ignore
                            so(a, b),
                            # skip
                            z3.BoolVal(True),
                        ),
                    ),
                    # a before b in XCY order
                    xcy(a, b),
                ),
            ),
        )


@cleanup
def test_antipode() -> None:
    # assert check(XCY.assertions())
    # all XCY executions are causally consistent
    assert compatible(CausalConsistency.assertions(), XCY.assertions())
