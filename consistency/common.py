from collections import namedtuple
from dataclasses import dataclass
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


@dataclass(unsafe_hash=True)
class Node:
    name: str
    layerable: list[type]    # list of classes with static medthod called `assertions`
    lbound: tuple[int, int] # min (inclusive) and max (inclusive) number of layers
    nonlayerable: list[type] # list of classes with static medthod called `assertions`
    nbound: tuple[int, int] # min (inclusive) and max (inclusive) number of nonlayerable


@dataclass(unsafe_hash=True)
class Edge:
    src: Node
    dests: list[Node]
    constraints: z3.AstRef


@cache
def powerset(s: Iterable) -> list:
    return list(chain.from_iterable(combinations(s, r) for r in range(len(s) + 1)))


def composable(nodes: list[Node], edges: list[Edge]) -> tuple[bool, dict]:
    model = dict()

    stack = list()
    visited = set()

    for node in nodes:
        stack.append(node)
        while stack:
            current = stack.pop()
            print(current.name, end=' ')
            if current not in visited:
                visited.add(current)
                for edge in edges:
                    if edge.src == current:
                        for dest in edge.dests:
                            if dest not in visited:
                                stack.append(dest)
                print(current.name, end=' ')
        print()

    return True, model
