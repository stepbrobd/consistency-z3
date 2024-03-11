from collections import namedtuple
from functools import cache
from inspect import getmro
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


@dataclass
class Node:
    name: str
    layerable: list[class] # list of classes with static medthod called `assertions`
    nonlayerable: list[class] # list of classes with static medthod called `assertions`


@dataclass
class Edge:
    src: Node
    dests: list[Node]
    constraints: z3.AstRef


@cache
def powerset(s: Iterable) -> list:
    return list(chain.from_iterable(combinations(s, r) for r in range(len(s) + 1)))


def composable(graph: dict) -> tuple[bool, dict]:
    class Empty:
        """
        a class that represents no semantics applied
        """
        @staticmethod
        def assertions() -> z3.BoolRef:
            return z3.BoolVal(False)

    session_guarantees = [
       MonotonicReads,
       MonotonicWrites,
       ReadYourWrites,
       WritesFollowReads,
    ]
    session_guarantees_powerset = powerset(tuple(session_guarantees))[1:] # remove the empty set
    # print(session_guarantees_powerset)
    # for g in session_guarantees_powerset:
    #     print([m.__name__ for m in g])

    model = dict() # TODO: add selected semantics to the model

    stack = []
    visited = set()
    k = next(iter(graph))
    v = next(iter(graph[k]))
    # stack.append((k, v))
    stack.append(next(iter(graph)))

    def can_visit(lhs: namedtuple, rhs: namedtuple) -> tuple[bool, str, str]:
        lhs_models = [m for m in lhs.semantics] + [Empty] if lhs.session_guarantees_applicable else [Empty]
        rhs_models = [m for m in rhs.semantics] + [Empty] if rhs.session_guarantees_applicable else [Empty]

        # use itertools to get all combinations of semantics
        for l, r in product(lhs_models, rhs_models):
            lname = getmro(l)[0].__name__
            rname = getmro(r)[0].__name__

            if compatible(l.assertions(), r.assertions()): # TODO: l and r can't be empty at the same time
                return True, lname, rname
            else:
                return False, lname, rname

    while len(stack) > 0:
        current = stack.pop()
        visited.add(current)

        for neighbor in graph[current]:
            # current is rhs, neighbor is lhs (neighbor should provide whatever guarantees current wants)
            print(f"origin: {current.name} -> target: {neighbor.name}")
            if neighbor not in visited:
                ok, n, c = can_visit(neighbor, current) # neighbor providing guarantees to current
                print(f"    => {c} -> {n}")
                if ok:
                    stack.append(neighbor)
            else:
                print("    => already visited")


    return len(visited) == len(graph), model
