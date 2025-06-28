import z3

from consistency.common import (
    Cons,
    Edge,
    Node,
    cleanup,
    composable,
    graph,
)
from consistency.model.linearizability import Linearizability
from consistency.model.pram_consistency import PRAMConsistency
from consistency.model.read_your_writes import ReadYourWrites


@cleanup
def test_trivial_succ() -> None:
    client = Node(name="Client", needs=[(Cons("LZ", Linearizability.assertions()),)], provs=None)
    api = Node(name="API", needs=[(Cons("RMW", ReadYourWrites.assertions()),)], provs=[(Cons("LZ", Linearizability.assertions()),)])
    storage = Node(name="Storage", needs=None, provs=[(Cons("RMW", ReadYourWrites.assertions()),)])

    nodes = [client, api, storage]
    edges = [
        Edge(src=client, dst=api, cons=None),
        Edge(src=api, dst=storage, cons=[(Cons("Nothing", z3.BoolVal(True)),)]),
    ]

    g = graph(nodes, edges)
    ok, res = composable(g, client)
    assert ok
    assert len(res.nodes) == 3
    assert len(res.edges) == 2


@cleanup
def test_trivial_fail() -> None:
    client = Node(name="Client", needs=[(Cons("LZ", Linearizability.assertions()),)], provs=None)
    api = Node(name="API", needs=[(Cons("PRAM", PRAMConsistency.assertions()),)], provs=[(Cons("LZ", Linearizability.assertions()),)])
    storage = Node(name="Storage", needs=None, provs=[(Cons("RMW", ReadYourWrites.assertions()),)])

    nodes = [client, api, storage]
    edges = [
        Edge(src=client, dst=api, cons=None),
        Edge(src=api, dst=storage, cons=[(Cons("Nothing", z3.BoolVal(False)),)]),
    ]

    g = graph(nodes, edges)
    ok, res = composable(g, client)
    assert not ok
    assert len(res.nodes) == 0
    assert len(res.edges) == 0
