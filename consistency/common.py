from collections import namedtuple
from functools import cache
from itertools import chain, combinations
from typing import Iterable

import z3

from consistency.model.monotonic_reads import MonotonicReads
from consistency.model.monotonic_writes import MonotonicWrites
from consistency.model.read_your_writes import ReadYourWrites
from consistency.model.writes_follow_reads import WritesFollowReads
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


def node(name: str, semantics: list[type], session_guarantees_applicable: bool) -> namedtuple:
    Node = namedtuple('Node', ['name', 'semantics', 'session_guarantees_applicable'])
    return Node(name, semantics, session_guarantees_applicable)


@cache
def powerset(s: Iterable) -> list:
    return list(chain.from_iterable(combinations(s, r) for r in range(len(s) + 1)))


def composable(graph: dict) -> bool:
    session_guarantees = [
       MonotonicReads,
       MonotonicWrites,
       ReadYourWrites,
       WritesFollowReads,
    ]
    powerset(tuple(session_guarantees))

    # TODO
    return False
