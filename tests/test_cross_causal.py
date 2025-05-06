from collections import Counter
from collections.abc import Callable

import z3

from consistency.common import (
    Cons,
    Edge,
    Node,
    cleanup,
    composable,
    compose,
    graph,
)
from consistency.model.monotonic_reads import MonotonicReads
from consistency.model.monotonic_writes import MonotonicWrites
from consistency.model.read_your_writes import ReadYourWrites
from consistency.model.writes_follow_reads import WritesFollowReads


@cleanup
def test_cross_causal() -> None:
    # dynamically generate semantics
    # for each storage system
    # src provs one session semantic
    # dst needs causal
    # from bottom up
    # should look like a converging binary tree
    # overall:
    # each node should export 1 semantic
    # edge connection that node to upper layer should provide
    # all missing semantics + "glue" constraints that connects different set of symbols
    #             xc
    #            / <- mr + mw + ryw
    #         svc4 - wfr
    #        / <- mr + mw + wfr
    #      svc3 - ryw
    #     / <- mr + ryw + wfr
    #   svc2 - mw
    #  / <- mw + ryw + wfr
    # svc1 (mr)

    # take in a str (semantic short hand name)
    # return a lambda that takes a str (sub system name) and list (of symbols)
    # final list should be a list of semantic_subsystem_symbol
    def gensym(name: str) -> Callable[[str, list[str]], list[str]]:
        return lambda s, symbols: [f"{name}_{s}_{symbol}" for symbol in symbols]

    # # semantic short hand name -> (assertion func, symbol gen)
    semantics = {
        "mr": (
            MonotonicReads.assertions,
            lambda s: gensym("mr")(s, ["a", "b", "c", "x"]),
        ),
        "mw": (MonotonicWrites.assertions, lambda s: gensym("mw")(s, ["a", "b", "c"])),
        "ryw": (
            ReadYourWrites.assertions,
            lambda s: gensym("ryw")(s, ["a", "b", "c", "x"]),
        ),
        "wfr": (
            WritesFollowReads.assertions,
            lambda s: gensym("wfr")(s, ["a", "b", "c", "x"]),
        ),
    }
    counter = Counter(semantics.keys())

    def assertion_for(name: str, sys: str) -> z3.BoolRef:
        assertion_func, symbol_gen = semantics[name]
        return assertion_func(symbol_gen(sys))

    svc1 = Node(
        name="SVC1",
        needs=None,
        provs=[(Cons("MR", assertion_for("mr", str(counter["mr"]))),)],
    )
    counter["mr"] += 1

    # SVC1 -> SVC2
    edge1_constraints = [
        assertion_for("mr", str(counter["mr"])),
        assertion_for("ryw", str(counter["ryw"])),
        assertion_for("wfr", str(counter["wfr"])),
    ]
    counter["mr"] += 1
    counter["ryw"] += 1
    counter["wfr"] += 1

    svc2 = Node(
        name="SVC2",
        needs=None,
        provs=[(Cons("MW", assertion_for("mw", str(counter["mw"]))),)],
    )
    counter["mw"] += 1

    edge1 = Edge(
        src=svc1,
        dst=svc2,
        cons=[(Cons("EC1", compose(*edge1_constraints)),)],
    )

    # SVC2 -> SVC3
    edge2_constraints = [
        assertion_for("mr", str(counter["mr"])),
        assertion_for("mw", str(counter["mw"])),
        assertion_for("wfr", str(counter["wfr"])),
    ]
    counter["mr"] += 1
    counter["mw"] += 1
    counter["wfr"] += 1

    svc3 = Node(
        name="SVC3",
        needs=None,
        provs=[(Cons("RYW", assertion_for("ryw", str(counter["ryw"]))),)],
    )
    counter["ryw"] += 1

    edge2 = Edge(
        src=svc2,
        dst=svc3,
        cons=[(Cons("EC2", compose(*edge2_constraints)),)],
    )

    # SVC3 -> SVC4
    edge3_constraints = [
        assertion_for("mr", str(counter["mr"])),
        assertion_for("mw", str(counter["mw"])),
        assertion_for("ryw", str(counter["ryw"])),
    ]
    counter["mr"] += 1
    counter["mw"] += 1
    counter["ryw"] += 1

    svc4 = Node(
        name="SVC4",
        needs=None,
        provs=[(Cons("WFR", assertion_for("wfr", str(counter["wfr"]))),)],
    )
    counter["wfr"] += 1

    edge3 = Edge(
        src=svc3,
        dst=svc4,
        cons=[(Cons("EC3", compose(*edge3_constraints)),)],
    )

    # SVC4 -> XC
    edge4_constraints = [
        assertion_for("mr", str(counter["mr"])),
        assertion_for("mw", str(counter["mw"])),
        assertion_for("ryw", str(counter["ryw"])),
    ]
    counter["mr"] += 1
    counter["mw"] += 1
    counter["ryw"] += 1

    xc = Node(
        name="XC",
        needs=None,
        provs=None,
    )

    edge4 = Edge(
        src=svc4,
        dst=xc,
        cons=[(Cons("EC4", compose(*edge4_constraints)),)],
    )

    # full graph
    nodes = [svc1, svc2, svc3, svc4, xc]
    edges = [edge1, edge2, edge3, edge4]

    g = graph(nodes, edges)
    ok, res = composable(g, svc1)
    # assert ok

    # sample extraction for further use
    # aggcons = extract(svc1, svc1, (ok, res))
    # Node(
    #     name="XC",
    #     needs=None,
    #     provs=[(Cons("XC", aggcons),)],
    # )

    """
    # loop based:
    # composition tree
    # [(name, prov, [to be added on edge])]
    ct = [
        ("svc1", "mr", ["mw", "ryw", "wfr"]),
        ("svc2", "mw", ["mr", "ryw", "wfr"]),
        ("svc3", "ryw", ["mr", "mw", "wfr"]),
        ("svc4", "wfr", ["mr", "mw", "ryw"]),
        ("xc", None, None)
    ]

    nodes = []
    edges = []

    # create all nodes
    for _i, (name, prov, _) in enumerate(ct):
        node_name = name.upper()

        if prov:
            # node with provs
            node = Node(
                name=node_name,
                needs=None,
                provs=[(Cons(prov.upper(), assertion_for(prov, str(counter[prov]))),)]
            )
            counter[prov] += 1
        else:
            # xc node dont prov anything
            node = Node(
                name=node_name,
                needs=None,
                provs=None
            )

        nodes.append(node)

    # edges between nodes
    for i in range(len(ct) - 1):
        src_node = nodes[i]
        dst_node = nodes[i+1]
        _, _, edge_semantics = ct[i]

        edge_constraints = []
        for sem in edge_semantics:
            edge_constraints.append(assertion_for(sem, str(counter[sem])))
            counter[sem] += 1

        edge = Edge(
            src=src_node,
            dst=dst_node,
            cons=[(Cons(f"EC{i+1}", compose(*edge_constraints)),)]
        )

        edges.append(edge)

    g = graph(nodes, edges)
    ok, res = composable(g, nodes[0])
    # assert ok

    # sample extraction for further use
    aggcons = extract(nodes[0], nodes[0], (ok, res))
    Node(
        name="XC",
        needs=None,
        provs=[(Cons("XC", aggcons),)],
    )
    """
