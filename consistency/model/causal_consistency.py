import z3

from consistency.abstract_execution import AbstractExecution as AE
from consistency.history import History as H
from consistency.model.model import Model
from consistency.operation import Operation as Op


class CausalConsistency(Model):
    @staticmethod
    def assertions() -> z3.BoolRef:
        op = Op.Create()
        _, (rd, wr) = Op.Sort()
        a, b = Op.Consts("a b")

        # writes-into: https://repository.gatech.edu/server/api/core/bitstreams/a083b72e-3e3d-4252-9f10-5ab71fa7f6c5/conten
        wi = H.Relation.Declare("wi", op, op, z3.BoolSort())
        H.Relation.AddConstraint("wi",
            z3.Implies(wi(a, b), z3.And(
                # a must be a write, b must be a read
                # a and b must be wr/rd on the same object (shared memory location)
                z3.If(op.type(a) == wr, z3.And(op.type(b) == rd, op.obj(a) == op.obj(b)), z3.BoolVal(True)),

            ))
        )

        so = H.Relation.session_order()
        ar = AE.Relation.arbitration()
        vis = AE.Relation.visibility()

        # PRAM + wi
        return z3.ForAll([a, b],
            z3.Implies(
                # may be incorrect?
                so(a, b),
                z3.And(wi(a, b), vis(a, b), ar(a, b))
            )
        )
