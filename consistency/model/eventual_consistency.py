import z3

from consistency.abstract_execution import AbstractExecution as AE
from consistency.model.model import Model
from consistency.model.rval import RVal
from consistency.operation import Operation as Op


# variants of eventual consistency' safety properties can be captured (i.e. strong convergence)
# but eventual visibility (the constraints guarenting the eventual delivery of ops are skipped)
# quiescent consistency cannot be modeled for now due to the same reason
class EventualWith(Model):
    @staticmethod
    def assertions(
        symbols: list[str] | None = None, ctx: z3.FuncDeclRef | None = None
    ) -> z3.BoolRef:
        if ctx is None:
            raise ValueError("Eventual consistency guiding ctx must be provided")

        if symbols is None:
            symbols = ["a", "b", "c", "x"]
        decl = " ".join(symbols)

        # _, (rd, wr) = Op.Sort()
        # op = Op.Create()
        a, b, *_ = Op.Consts(decl)
        hb = AE.Relation.happens_before()

        # eventual visibility
        # eventually, op will be visible to op'
        # invoked after the completion of op
        eventual_visibility = z3.BoolVal(True)

        # acyclic projection of hb
        no_circular_causality = z3.ForAll(
            [a, b],
            z3.Implies(
                hb(a, b),
                z3.Not(hb(b, a)),
            ),
        )

        # return value consistency specifies the return value consistency of a replicated data type
        rval = RVal.assertions(symbols, ctx)

        return z3.And(eventual_visibility, no_circular_causality, rval)  # type: ignore


class EventualConsistency(Model):
    @staticmethod
    def assertions(symbols: list[str] | None = None) -> z3.BoolRef:
        return EventualWith.assertions(
            symbols, AE.Relation.can_view(symbols) # can view is the weakest value equivalence relation
        )
