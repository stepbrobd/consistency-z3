from dataclasses import dataclass
from functools import cache
from itertools import chain, combinations, product
from typing import Iterable

import z3

from consistency.relation import Relation


def check(assertions: z3.BoolRef, others: z3.AstRef = z3.BoolVal(True)) -> bool:
    s = z3.Solver()
    s.add([assertions, Relation.Constraints(), others])
    return s.check() == z3.sat


def compatible(lhs: z3.BoolRef, rhs: z3.BoolRef, others: z3.AstRef = z3.BoolVal(True)) -> bool:
    # assert the negation of lhs (base) => rhs (target) is unsatisfiable
    # i.e. lhs implies rhs holds for all enumerated cases
    s = z3.Solver()
    s.add([z3.Not(z3.Implies(lhs, rhs)), Relation.Constraints(), others])
    return s.check() == z3.unsat


def compose(*assertions: z3.BoolRef) -> z3.BoolRef:
    # direct conjunction of all provided **boolean** constraints
    return z3.And(*[assertion for assertion in assertions if assertion is not None])


@dataclass(unsafe_hash=True)
class Cons:
    name: str
    cons: z3.AstRef


@dataclass(unsafe_hash=True)
class Node:
    name: str
    needs: list[tuple[Cons]] | None # list of required semantics
    provs: list[tuple[Cons]] | None # list of provided semantics


@dataclass(unsafe_hash=True)
class Edge:
    src: Node
    dst: Node
    cons: list[tuple[Cons]] | None  # additional constraints


@cache
def powerset(s: Iterable) -> list:
    return list(chain.from_iterable(combinations(s, r) for r in range(len(s) + 1)))


def composable(nodes: list[Node], edges: list[Edge]) -> tuple[bool, list]:
    """
    disjoint nodes might be present in the graph
    returns: whether there's one possible composable assignment, list of resulting assignments
    """
    composable = False
    na = [(Cons("N/A", z3.BoolVal(False)),)]
    visited = set()

    # go through all edges
    edge_result = []
    for edge in edges:
        src = edge.src
        dst = edge.dst
        # unwrap edge cons with direct conjunction
        ec = z3.BoolVal(True) # if no edge constraints, simply set it to True
        if edge.cons:
            for t in edge.cons: # for terms in edge constraints
                for c in t: # for each constraint in term
                    if c: # if exists
                        # note that `compose` will do direct conjunctions on all provided **boolean** constraints
                        ec = compose(ec, c.cons) # use True as governing constraint, conjunct with raw z3 clauses

        for sn, sp, dn, dp in product( # generate all possible combinations of needs and provs for src and dst
            na if not src.needs else src.needs,
            na if not src.provs else src.provs,
            na if not dst.needs else dst.needs,
            na if not dst.provs else dst.provs,
        ): # brute force all possible combinations
            for asn, asp, adn, adp in product(sn, sp, dn, dp): # for each combination
                # direct conjunction of all source node "needs" constraints + edge constraints
                # then assert the result to destination node "provs" constraints
                sat = compatible(adp.cons, compose(asn.cons, ec))
                if sat:
                    composable = True
                edge_result.append((edge, asn, asp, adn, adp, sat))

        visited.add(edge.src.name)

    # go through all disjoint nodes (tho might not be necessary)
    for node in [n if n.name not in visited else None for n in nodes]:
        if node is None:
            continue

        # print(node)

    return composable, edge_result
