import z3

from consistency.abstract_execution import AbstractExecution as AE
from consistency.common import compose
from consistency.history import History as H
from consistency.model.model import Model
from consistency.model.writes_follow_reads import WritesFollowReads
from consistency.operation import Operation as Op


class CausalConsistency(Model):
    @staticmethod
    def assertions(symbols: list[str] | None = None) -> z3.BoolRef:
        if symbols is None:
            symbols = ["a", "b", "c"]
        decl = " ".join(symbols)

        op = Op.Create()
        _, (rd, wr) = Op.Sort()
        a, b, c, *_ = Op.Consts(decl)

        so = H.Relation.session_order()
        ar = AE.Relation.arbitration()
        vis = AE.Relation.visibility()

        # writes-into: https://repository.gatech.edu/server/api/core/bitstreams/a083b72e-3e3d-4252-9f10-5ab71fa7f6c5/content
        wi = H.Relation.Declare("wi", op, op, z3.BoolSort())
        H.Relation.AddConstraint("wi",
            z3.Implies(wi(a, b), z3.And( # type: ignore
                # a must be a write, b must be a read
                # a and b must be wr/rd on the same object (shared memory location)
                z3.If(op.type(a) == wr, z3.And(op.type(b) == rd, op.obj(a) == op.obj(b)), z3.And( # type: ignore
                    ar(a, b),
                    # values must match
                    op.ival(a) == op.oval(b), # type: ignore
                    # at most one write a can write-into a read b
                    z3.ForAll([a, b, c], z3.Implies(z3.And(op.type(c) == rd, wi(a, b)), z3.Not(wi(a, c)))), # type: ignore
                )),
                # acyclicity
                z3.ForAll([a, b], z3.Implies(wi(a, b), z3.Not(wi(b, a)))),
            ))
        )

        # session causality (enforced by WRF) + writes-into
        return compose(WritesFollowReads.assertions(), z3.ForAll([a, b],
            z3.Implies(
                so(a, b),
                z3.And(wi(a, b), vis(a, b), ar(a, b))
            )
        ))
