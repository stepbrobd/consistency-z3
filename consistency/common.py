import pathlib
from collections.abc import Callable, Collection, Generator
from functools import cache, wraps
from itertools import chain, combinations, product
from typing import (
    Literal,
    NamedTuple,
    ParamSpec,
    TypeVar,
    overload,
)

import matplotlib.pyplot as plt
import networkx as nx
import z3

from consistency.relation import Relation

P = ParamSpec("P")
R = TypeVar("R")


@overload
def cleanup(func: Callable[P, R]) -> Callable[P, R]: ...
# for type hinting only


@overload
def cleanup() -> Callable[[Callable[P, R]], Callable[P, R]]: ...
# for type hinting only


def cleanup(
    func: Callable[P, R] | None = None,
) -> Callable[P, R] | Callable[[Callable[P, R]], Callable[P, R]]:
    # use this decorator to reset constraint singletons
    def decorator(f: Callable[P, R]) -> Callable[P, R]:
        @wraps(f)
        def wrapper(*args: P.args, **kwargs: P.kwargs) -> R:
            try:
                return f(*args, **kwargs)
            finally:
                from consistency.history import History as H

                H.Relation.Reset()
                from consistency.abstract_execution import AbstractExecution as AE

                AE.Relation.Reset()

        return wrapper

    if func is None:
        return decorator
    return decorator(func)


def params() -> None:
    # why is pyz3 and z3 showing different mbqi behaviors?
    """
    z3 \
      verbose=3 \
      parallel.enable=true \
      sat.local_search_threads=32 \
      sat.ddfw_search=true \
      sat.ddfw.threads=32 \
      smt.mbqi.trace=true \
      smt.pull_nested_quantifiers=true \
      -smt2 <file>.smt2
    """
    z3.set_param("parallel.enable", True)
    # z3.set_param("smt.mbqi.trace", True)
    z3.set_param("smt.pull_nested_quantifiers", True)
    # z3.set_param("smtlib2_compliant", True)
    z3.set_param("sat.local_search_threads", 32)
    z3.set_param("sat.ddfw_search", True)
    z3.set_param("sat.ddfw.threads", 32)


def check(
    assertions: z3.BoolRef,
    others: z3.AstRef = z3.BoolVal(True),
    witness: pathlib.Path | None = None,
) -> bool:
    s = z3.SolverFor("QF_LRA")
    params()
    s.add([assertions, Relation.Constraints(), others])

    if witness:
        with witness.open("w") as f:
            f.write(s.to_smt2())

    # return s.check() == z3.sat
    result = s.check()
    # model = s.model()
    # print(model)
    # print(model.eval(assertions))
    # print(s.unsat_core())
    return result == z3.sat


def construct(
    lhs: z3.BoolRef,
    rhs: z3.BoolRef,
    others: z3.AstRef = z3.BoolVal(True),
) -> z3.Solver:
    # assert the negation of lhs (base) => rhs (target) is unsatisfiable
    # i.e. lhs implies rhs holds for all enumerated cases
    s = z3.SolverFor("QF_LRA")
    params()
    s.add(others)
    s.add(z3.Not(z3.Implies(lhs, rhs)), Relation.Constraints())
    return s


def compatible(
    lhs: z3.BoolRef,
    rhs: z3.BoolRef,
    others: z3.AstRef = z3.BoolVal(True),
    witness: pathlib.Path | None = None,
) -> bool:
    s = construct(lhs, rhs, others)

    if witness:
        with witness.open("w") as f:
            f.write(s.to_smt2())

    result = s.check() == z3.unsat
    # print(solver.to_smt2())
    # if result:
    #     print(solver.unsat_core())
    # print(solver.statistics())
    return result


def compose(*assertions: z3.BoolRef) -> z3.BoolRef:
    # direct conjunction of all provided **boolean** constraints
    return z3.And(*[assertion for assertion in assertions if assertion is not None])  # type: ignore


class Cons(NamedTuple):
    name: str
    cons: z3.AstRef


class Node(NamedTuple):
    name: str
    needs: list[tuple[Cons]] | None  # list of required semantics
    provs: list[tuple[Cons]] | None  # list of provided semantics


class Edge(NamedTuple):
    src: Node
    dst: Node
    cons: list[tuple[Cons]] | None  # additional constraints


@cache
def powerset(s: Collection) -> list:
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


def plot(g: nx.MultiDiGraph) -> plt.Figure:  # type: ignore
    # modified from networkx example
    # https://networkx.org/documentation/stable/auto_examples/drawing/plot_clusters.html
    communities = nx.community.greedy_modularity_communities(g)

    # compute positions for the node clusters as if they were themselves nodes in a
    # supergraph using a larger scale factor
    superpos = nx.spring_layout(g)

    # use the "supernode" positions as the center of each node cluster
    centers = list(superpos.values())
    pos = {}
    for center, comm in zip(centers, communities, strict=False):
        pos.update(nx.spring_layout(nx.subgraph(g, comm), center=center))

    # color generator
    def colors(size: int) -> Generator[str, None, None]:
        counter = 0
        clrs = [
            f"tab:{clr}"
            for clr in (
                "blue",
                "orange",
                "green",
                "red",
                "purple",
                "cyan",
                "magenta",
                "yellow",
            )
        ]
        while counter < size:
            yield clrs[counter % len(clrs)]
            counter += 1

    # nodes colored by cluster
    for nodes, clr in zip(communities, colors(len(communities)), strict=False):
        nx.draw_networkx_nodes(g, pos=pos, nodelist=nodes, node_color=clr)

    nx.draw_networkx_labels(g, pos=pos)

    # only draws straight edges
    # nx.draw_networkx_edges(g, arrows=True, pos=pos)
    # draw edges with curves
    # https://stackoverflow.com/a/60641770/17129151
    ax = plt.gca()
    for e in g.edges:
        ax.annotate(
            "",
            xy=pos[e[0]],
            xycoords="data",
            xytext=pos[e[1]],
            textcoords="data",
            arrowprops=dict(
                arrowstyle="<-",
                color="0",
                shrinkA=5,
                shrinkB=5,
                patchA=None,
                patchB=None,
                connectionstyle="arc3,rad=rrr".replace("rrr", str(0.3 * e[2])),  # type: ignore
            ),
        )

    plt.tight_layout()
    figure = plt.get_current_fig_manager().canvas.figure  # type: ignore
    return figure


def composable(
    graph: nx.MultiDiGraph,
    source: Node,
    premise: z3.BoolRef = z3.BoolVal(True),
    witness: pathlib.Path | None = None,  # TODO: might or might not implement
) -> tuple[bool, nx.MultiDiGraph]:
    if witness:
        raise NotImplementedError(
            "witness generation for `composable` check not implemented yet"
        )

    # returns whether there's one possible composable assignment
    # and the first satisfying assignment
    result = nx.MultiDiGraph()
    edge_na = [(Cons("N/A", z3.BoolVal(True)),)]
    node_prov_na = [(Cons("N/A", z3.BoolVal(False)),)]
    node_need_na = edge_na

    def get_outgoing_edges(node_name: str) -> dict[tuple[str, str], list[int]]:
        # get all outgoing edges grouped by source-destination pairs
        edges: dict[tuple[str, str], list[int]] = {}
        for u, v, k in graph.edges(node_name, keys=True):  # type: ignore
            edges.setdefault((u, v), []).append(k)
        return edges

    def traverse(curr_node: str, visited_edges: set, path_premise: z3.BoolRef) -> bool:
        # DFS traverse with backtracking:
        # curr_node: current node name
        # visited_edges: set of (u, v, k) tuples of visited edges
        # path_premise: accumulated constraints from path so far
        # success if we've visited all edges
        if len(visited_edges) == graph.number_of_edges():
            return True

        # get unvisited outgoing edges grouped by dst node
        outgoing = get_outgoing_edges(curr_node)
        unvisited_pairs = {
            (u, v): keys
            for (u, v), keys in outgoing.items()
            if not all((u, v, k) in visited_edges for k in keys)
        }

        # if no unvisited outgoing edges from current node,
        # try continuing from any node that has unvisited outgoing edges
        if not unvisited_pairs:
            for node in graph.nodes():
                if node == curr_node:
                    continue
                node_outgoing = get_outgoing_edges(node)
                unvisited_from_node = {
                    (u, v): keys
                    for (u, v), keys in node_outgoing.items()
                    if not all((u, v, k) in visited_edges for k in keys)
                }
                if unvisited_from_node:
                    if traverse(node, visited_edges, path_premise):
                        return True
            return False

        # try each unvisited src-dst pair
        # u: src, v: dst, k: edge id in nx
        for (u, v), edge_keys in unvisited_pairs.items():
            src_node = Node(**graph.nodes[u])
            dst_node = Node(**graph.nodes[v])
            # print(f"{u} -> {v}")

            # all unvisited edges between this pair
            unvisited_keys = [k for k in edge_keys if (u, v, k) not in visited_edges]

            # combinations for src.needs and dst.provs
            src_needs = src_node.needs if src_node.needs else [node_need_na[0]]
            dst_provs = dst_node.provs if dst_node.provs else [node_prov_na[0]]
            # try each combination
            for needs, provs in product(src_needs, dst_provs):
                check_needs = compose(*[n.cons for n in needs])  # type: ignore
                check_provs = compose(*[p.cons for p in provs])  # type: ignore

                # track edges that pass checks at this level
                valid_edges = []
                edge_constraints = []

                # check all edges between this pair with same premise
                for k in unvisited_keys:
                    edge_data = graph.get_edge_data(u, v, k)
                    edge_cons = edge_data["cons"] if edge_data["cons"] else [edge_na[0]]

                    # try each edge constraint
                    for cons in edge_cons:
                        check_ec = compose(*[c.cons for c in cons])  # type: ignore

                        # check compatibility with path so far
                        if compatible(
                            check_provs, compose(check_needs, check_ec), path_premise
                        ):
                            valid_edges.append(k)
                            edge_constraints.append(cons)

                # case 1:
                # if all edges between this pair are valid
                if len(valid_edges) == len(unvisited_keys):
                    # add all valid edges to visited and results
                    for k, cons in zip(valid_edges, edge_constraints, strict=False):
                        visited_edges.add((u, v, k))

                        # add to resulting graph
                        if not result.has_node(u):
                            result.add_node(u, needs=[needs], provs=src_node.provs)
                        if not result.has_node(v):
                            result.add_node(v, needs=dst_node.needs, provs=[provs])
                        result.add_edge(u, v, key=k, cons=[cons])

                    # compose new premise
                    # since 'others' is added as a separate constraint in the solver
                    # include all constraints from the current level
                    all_ec = compose(
                        *[compose(*[c.cons for c in cons]) for cons in edge_constraints]
                    )
                    new_premise = compose(
                        path_premise, check_provs, check_needs, all_ec
                    )

                    # continue DFS:
                    # try continuing from either the destination node or any other node with unvisited edges
                    if traverse(v, visited_edges, new_premise):
                        return True

                    # backtrack: remove all previously added nodes and edges
                    for k in valid_edges:
                        result.remove_edge(u, v, k)
                        visited_edges.remove((u, v, k))
                    if result.degree(u) == 0:
                        result.remove_node(u)
                    if result.degree(v) == 0:
                        result.remove_node(v)

                # case 2:
                # also backtrack if no valid edges found for the current level
                else:
                    # clean up partial progress
                    for k in valid_edges:
                        if result.has_edge(u, v, k):
                            result.remove_edge(u, v, k)
                        if (u, v, k) in visited_edges:
                            visited_edges.remove((u, v, k))
                    if result.has_node(u) and result.degree(u) == 0:
                        result.remove_node(u)
                    if result.has_node(v) and result.degree(v) == 0:
                        result.remove_node(v)

        return False

    # start DFS from src
    is_composable = traverse(source.name, set(), premise)
    # replace all N/A with None
    for node in result.nodes():
        if result.nodes[node]["needs"] == node_need_na:
            result.nodes[node]["needs"] = None
        if result.nodes[node]["provs"] == node_prov_na:
            result.nodes[node]["provs"] = None
    for edge in result.edges(keys=True):  # type: ignore
        if result.get_edge_data(*edge)["cons"] == edge_na:
            result.get_edge_data(*edge)["cons"] = None
    return is_composable, result


"""
def composable(nodes: list[Node], edges: list[Edge]) -> tuple[bool, list]:
    # disjoint nodes might be present in the graph
    # returns: whether there's one possible composable assignment, list of resulting assignments
    composable = False
    node_na = [(Cons("N/A", z3.BoolVal(False)),)]
    edge_na = [(Cons("N/A", z3.BoolVal(True)),)]
    visited = set()

    # go through all edges
    edge_result = []
    for edge in edges:
        src = edge.src
        dst = edge.dst
        # unwrap edge cons with direct conjunction
        ec = edge_na[0][0].cons # if no edge constraints, simply set it to True
        if edge.cons:
            for t in edge.cons: # for terms in edge constraints
                for c in t: # for each constraint in term
                    if c: # if exists
                        # note that `compose` will do direct conjunctions on all provided **boolean** constraints
                        ec = compose(ec, c.cons) # use True as governing constraint, conjunct with raw z3 clauses

        for sn, sp, dn, dp in product( # generate all possible combinations of needs and provs for src and dst
            node_na if not src.needs else src.needs,
            node_na if not src.provs else src.provs,
            node_na if not dst.needs else dst.needs,
            node_na if not dst.provs else dst.provs,
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
"""


def dfs(
    graph: nx.MultiDiGraph, src: str
) -> Generator[tuple[Node, Node, z3.AstRef], None, None]:
    # yields src node, dst node, and edge constraints in DFS order
    # only works if the graph has _single_ constraint assignment
    # i.e. the resulting graph from `composable` call
    for name_src, name_dst, key, _ in nx.edge_dfs(
        graph, source=src, orientation="original"
    ):
        node_src = Node(name_src, **graph.nodes[name_src])
        node_dst = Node(name_dst, **graph.nodes[name_dst])
        edge_data = graph.get_edge_data(name_src, name_dst, key)["cons"]
        try:
            edge_cons = edge_data[0][0].cons
        except (AttributeError, TypeError):
            edge_cons = z3.BoolVal(True)
        yield node_src, node_dst, edge_cons


def extract(
    inode: Node, onode: Node, compose_result: tuple[bool, nx.MultiDiGraph]
) -> z3.AstRef:
    # extract equivalent constraints from `compose` result
    # inode: aggregate node's constraint flow entrance
    # onode: aggregate node's constraint flow exit
    # disallow extraction when inode and onode are different
    if inode.name != onode.name:
        raise NotImplementedError(
            "inode and onode must be the same, please refer to docs"
        )

    composable, graph = compose_result
    assert composable, "No composable assignment found"

    aggcons = []

    def get_node_cons(node: Node, attr: Literal["needs", "provs"]) -> z3.AstRef:
        try:
            return node._asdict()[attr][0][0].cons
        except (AttributeError, TypeError):
            return z3.BoolVal(True)

    # if inode and onode are the same
    # conjunct reachable node& edge constraints from inode
    for src, dst, ec in dfs(graph, inode.name):
        aggcons.append(
            compose(get_node_cons(src, "provs"), ec, get_node_cons(dst, "needs"))  # type: ignore
        )

    return compose(*aggcons)
