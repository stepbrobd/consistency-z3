from functools import cache
from itertools import chain, combinations, product
from typing import Generator, Iterable, Literal, NamedTuple

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

    nx.draw_networkx_labels(g, pos=pos)

    # only draws straight edges
    # nx.draw_networkx_edges(g, arrows=True, pos=pos)
    # draw edges with curves
    # https://stackoverflow.com/a/60641770/17129151
    ax = plt.gca()
    for e in g.edges:
        ax.annotate("", xy=pos[e[0]], xycoords="data",
            xytext=pos[e[1]], textcoords="data",
            arrowprops=dict(
                arrowstyle="<-", color="0",
                shrinkA=5, shrinkB=5,
                patchA=None, patchB=None,
                connectionstyle="arc3,rad=rrr".replace('rrr',str(0.3*e[2])),
            ),
        )

    plt.tight_layout()
    figure = plt.get_current_fig_manager().canvas.figure
    return figure


def composable_v2(graph: nx.MultiDiGraph, source: Node, premise: z3.BoolRef=z3.BoolVal(True)) -> tuple[bool, nx.MultiDiGraph]:
    # method must be one of the functions in nx.algorithms.traversal that traverse over edges
    # returns whether there's one possible composable assignment
    # and the first satisfying assignment
    # premise will be directly added to the solver as the context
    composable = False
    results = nx.MultiDiGraph()

    na = [(Cons("N/A", z3.Empty(z3.BoolSort())),)]

    plan: list[Edge] = []
    for edge in nx.algorithms.traversal.edge_dfs(graph, source=source.name, orientation="original"):
        edge: tuple[str, str, int, Literal["forward", "reverse"]]
        src, dst, key, _ = edge # _: direction
        src_node = Node(**graph.nodes[src])
        dst_node = Node(**graph.nodes[dst])
        cons = graph.get_edge_data(src, dst, key)["cons"]
        plan.append(Edge(src_node, dst_node, cons))

    # source node is the src of the first edge
    def traverse(visited: list[Edge|None], planned: list[Edge|None]) -> None:
        nonlocal composable

        if not planned:
            return

        e = planned.pop(0)
        src, dst, ec = e.src, e.dst, e.cons

        chosen = Edge(Node(src.name, ..., ...), Node(dst.name, ..., ...), ...) # TODO: replace ... with a single Cons picked from the available choices
        visited.append(chosen)

    traverse([], plan)

    return composable, results


def composable(nodes: list[Node], edges: list[Edge]) -> tuple[bool, list]:
    """
    disjoint nodes might be present in the graph
    returns: whether there's one possible composable assignment, list of resulting assignments
    """
    composable = False
    na = [(Cons("N/A", z3.Empty(z3.BoolSort())),)]
    visited = set()

    # go through all edges
    edge_result = []
    for edge in edges:
        src = edge.src
        dst = edge.dst
        # unwrap edge cons with direct conjunction
        ec = na[0][0].cons # if no edge constraints, simply set it to True
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
                else:
                    print("Not Composable")
                edge_result.append((edge, asn, asp, adn, adp, sat))

        visited.add(edge.src.name)

    # go through all disjoint nodes (tho might not be necessary)
    for node in [n if n.name not in visited else None for n in nodes]:
        if node is None:
            continue

        # print(node)

    return composable, edge_result
