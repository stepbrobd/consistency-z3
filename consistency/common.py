from functools import cache
from itertools import chain, combinations, product
from typing import Generator, Iterable, NamedTuple

import matplotlib.pyplot as plt
import networkx as nx
import z3

from consistency.relation import Relation


def check(assertions: z3.BoolRef, others: z3.AstRef = z3.BoolVal(True)) -> bool:
    s = z3.Solver()
    s.add([assertions, Relation.Constraints(), others])
    return s.check() == z3.sat


def construct(lhs: z3.BoolRef, rhs: z3.BoolRef, others: z3.AstRef = z3.BoolVal(True)) -> z3.Solver:
    # assert the negation of lhs (base) => rhs (target) is unsatisfiable
    # i.e. lhs implies rhs holds for all enumerated cases
    s = z3.Solver()
    s.add([z3.Not(z3.Implies(lhs, rhs)), Relation.Constraints(), others])
    return s


def compatible(lhs: z3.BoolRef, rhs: z3.BoolRef, others: z3.AstRef = z3.BoolVal(True)) -> bool:
    return construct(lhs, rhs, others).check() == z3.unsat


def compose(*assertions: z3.BoolRef) -> z3.BoolRef:
    # direct conjunction of all provided **boolean** constraints
    return z3.And(*[assertion for assertion in assertions if assertion is not None])


class Cons(NamedTuple):
    name: str
    cons: z3.AstRef


class Node(NamedTuple):
    name: str
    needs: list[tuple[Cons]] | None # list of required semantics
    provs: list[tuple[Cons]] | None # list of provided semantics


class Edge(NamedTuple):
    src: Node
    dst: Node
    cons: list[tuple[Cons]] | None  # additional constraints


@cache
def powerset(s: Iterable) -> list:
    return list(chain.from_iterable(combinations(s, r) for r in range(len(s) + 1)))


def graph(nodes: list[Node], edges: list[Edge]) -> nx.MultiDiGraph:
    g = nx.MultiDiGraph()

    for node in nodes:
        g.add_node(node.name, **node._asdict())
    for edge in edges:
        g.add_edge(edge.src.name, edge.dst.name, **edge._asdict())

    # import matplotlib.pyplot as plt
    # nx.draw(g, with_labels=True)
    # plt.show()

    return g


def plot(g: nx.MultiDiGraph) -> plt.Figure:
    # modified from networkx example
    # https://networkx.org/documentation/stable/auto_examples/drawing/plot_clusters.html
    communities = nx.community.greedy_modularity_communities(g)

    # compute positions for the node clusters as if they were themselves nodes in a
    # supergraph using a larger scale factor
    superpos = nx.spring_layout(g)

    # use the "supernode" positions as the center of each node cluster
    centers = list(superpos.values())
    pos = {}
    for center, comm in zip(centers, communities):
        pos.update(nx.spring_layout(nx.subgraph(g, comm), center=center))

    # color generator
    def colors(size: int) -> Generator[str, None, None]:
        counter = 0
        clrs = [f"tab:{clr}" for clr in ("blue", "orange", "green", "red", "purple", "cyan", "magenta", "yellow")]
        while counter < size:
            yield clrs[counter % len(clrs)]
            counter += 1

    # nodes colored by cluster
    for nodes, clr in zip(communities, colors(len(communities))):
        nx.draw_networkx_nodes(g, pos=pos, nodelist=nodes, node_color=clr)
    nx.draw_networkx_edges(g, arrows=True, pos=pos)
    nx.draw_networkx_labels(g, pos=pos)

    plt.tight_layout()
    figure = plt.get_current_fig_manager().canvas.figure
    return figure


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
                # print(f"Source Node Needs: {asn.name} | Destination Node Provides: {adp.name} | Edge Constraints: {ec}")
                # direct conjunction of all source node "needs" constraints + edge constraints
                # then assert the result to destination node "provs" constraints
                sat = compatible(adp.cons, compose(asn.cons, ec))
                if sat:
                    composable = True
                else: print("Not Composable")
                edge_result.append((edge, asn, asp, adn, adp, sat))

        visited.add(edge.src.name)

    # go through all disjoint nodes (tho might not be necessary)
    for node in [n if n.name not in visited else None for n in nodes]:
        if node is None:
            continue

        # print(node)

    return composable, edge_result
