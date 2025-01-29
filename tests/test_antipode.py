import z3

from consistency.abstract_execution import AbstractExecution as AE
from consistency.history import History as H
from consistency.operation import Operation as Op
from consistency.relation import Relation as Rel


def test_antipode() -> None:
    # predicates
    _, (rd, wr) = Op.Sort()
    op = Op.Create()
    a, b, x, y, z = Op.Consts("a b x y z")

    hb = AE.Relation.happens_before()
    ar = AE.Relation.arbitration()
    so = H.Relation.same_object()
    rb = H.Relation.returns_before()
    vis = AE.Relation.visibility()

    # FIXME: temporary scaffolding
    # review lineage and xcy defs
    class Antipode:
        class Relation(Rel):
            @staticmethod
            def lineage() -> z3.FuncDeclRef:
                lineage = AE.Relation.Declare("lineage", op, op, z3.BoolSort())

                Antipode.Relation.AddConstraint(
                    "lineage",
                    z3.And(  # type: ignore
                        # 0. DAG: acyclicity and transitivity
                        z3.ForAll(
                            [a, b], z3.Implies(lineage(a, b), z3.Not(lineage(b, a)))
                        ),
                        z3.ForAll(
                            [a, x, b],
                            z3.Implies(
                                z3.And(lineage(a, x), lineage(x, b)),
                                lineage(a, b),
                            ),
                        ),
                        # 1. single root
                        # 2. strict ordering within the same process of a lineage
                        z3.If(op.proc(a) == op.proc(b), ar(a, b), z3.BoolVal(True)),  # type: ignore
                        # 3. weak object/value equivalence
                        z3.Or(
                            op.obj(a) == op.obj(b),  # type: ignore
                            op.ival(a) == op.oval(b),  # a:wr; b:rd # type: ignore
                            op.oval(a) == op.oval(b),  # a:rd; b:rd # type: ignore
                        ),
                        # 4. invocation correspondence
                        z3.BoolVal(True),
                        # 5. reply correspondence
                        z3.BoolVal(True),
                    ),
                )

                return lineage

            @staticmethod
            def xcy() -> z3.FuncDeclRef:
                lineage = Antipode.Relation.lineage()

                xcy = AE.Relation.Declare("xcy", op, op, z3.BoolSort())

                AE.Relation.AddConstraint(
                    "xcy",
                    z3.Implies(
                        xcy(a, b),
                        z3.And(  # type: ignore
                            # 1. lanport happened-before
                            z3.BoolVal(True),
                            # 2. read-from-lineage
                            # barrier enforced here?
                            # https://github.com/Antipode-SOSP23/antipode-deathstarbench
                            # https://github.com/Antipode-SOSP23/antipode-post-notification/blob/892a8c16922b1f4ec60dc6700f1ffca8629d5fc7/lambdas/reader.py#L63
                            z3.If(
                                z3.And(
                                    op.type(y) == wr, op.type(b) == rd
                                ),  # TODO # type: ignore
                                z3.And(
                                    lineage(a, b),
                                    z3.ForAll(
                                        [a], z3.BoolVal(True)
                                    ),  # FIXME # type: ignore
                                ),
                                z3.BoolVal(False),
                            ),
                            # 3. transitivity
                            z3.ForAll(
                                x,
                                z3.Implies(
                                    z3.And(xcy(a, x), xcy(x, b)),
                                    xcy(a, b),
                                ),
                            ),
                        ),
                    ),
                )

                return xcy
