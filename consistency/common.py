import z3

from consistency.relation import Relation


def check(assertions: z3.BoolRef, others: z3.AstRef = z3.BoolVal(True)) -> bool:
    s = z3.Solver()
    s.add([assertions, Relation.Constraints(), others])
    return s.check() == z3.sat


def compatible(lhs: z3.BoolRef, rhs: z3.BoolRef, others: z3.AstRef = z3.BoolVal(True)) -> bool:
    s = z3.Solver()
    s.add([z3.Not(z3.Implies(lhs, rhs)), Relation.Constraints(), others])
    return s.check() == z3.unsat


def compose(*assertions: z3.BoolRef) -> z3.BoolRef:
    return z3.And(*assertions)
