from collections import namedtuple
from functools import cache
from itertools import chain, combinations, product
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

    # debug
    # for t in session_guarantees_powerset:
    #     print(f"[" + ", ".join([x.__name__ for x in t]) + "]")

    stack = []
    visited = set()
    stack.append(next(iter(graph)))

    # for i, (rhs, lhss) in enumerate(graph.items()):
    #     print(f"iteration {i}")

    #     for lhs in lhss:
    #         print(f"origin: {rhs.name} -> target: {lhs.name}")
    #         # false here means no semantic is applied
    #         lhs_assertions = [x.assertions() for x in lhs.semantics] + [z3.BoolVal(False)]
    #         print(f"lhs_assertions: {len(lhs_assertions)}")

    def can_visit(lhs: namedtuple, rhs: namedtuple) -> bool:
        lhs_assertions = [x.assertions() for x in lhs.semantics] + [z3.BoolVal(False)] \
                if lhs.session_guarantees_applicable \
                else [z3.BoolVal(False)]
        rhs_assertions = [x.assertions() for x in rhs.semantics] + [z3.BoolVal(False)] \
                if rhs.session_guarantees_applicable \
                else [z3.BoolVal(False)]

        # use itertools to get all combinations of semantics
        for lhs, rhs in product(lhs_assertions, rhs_assertions):
            if compatible(lhs, rhs):
                return True

        return False

    while len(stack) > 0:
        current = stack.pop()
        visited.add(current)

        for neighbor in graph[current]:
            # current is rhs, neighbor is lhs (neighbor should provide whatever guarantees current wants)
            print(f"origin: {current.name} -> target: {neighbor.name}")
            if neighbor not in visited and can_visit(neighbor, current):
                stack.append(neighbor)


    return len(visited) == len(graph)
