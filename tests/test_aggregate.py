
from consistency.common import (
    Cons,
    Edge,
    Node,
    composable,
    compose,
    extract,
    graph,
)
from consistency.model.linearizability import Linearizability
from consistency.model.monotonic_reads import MonotonicReads
from consistency.model.read_your_writes import ReadYourWrites


def test_shop() -> None:
    arbitrator = Node(
        name="Arbitrator",
        needs=None,
        provs=[(Cons("LZ", Linearizability.assertions()),)],
    )
    tx = Node(
        name="Tx", needs=None, provs=[(Cons("LZ", Linearizability.assertions()),)]
    )
    shop = Node(
        name="Shop",
        needs=None,
        provs=[
            (
                Cons(
                    "RMW+MR",
                    compose(ReadYourWrites.assertions(), MonotonicReads.assertions()),
                ),
            )
        ],
    )

    nodes = [arbitrator, tx, shop]
    edges = [
        Edge(src=arbitrator, dst=shop, cons=None),
        Edge(src=arbitrator, dst=tx, cons=None),
    ]

    g = graph(nodes, edges)
    ok, res = composable(g, arbitrator)
    assert ok

    # import matplotlib.pyplot as plt
    # from consistency.common import plot
    # plot(g)
    # plt.show()

    # in actual modeling, inode and onode might be different
    # be sure to add the inode and onode to nodes list
    # and connect all nodes with in degree of 1 from the inode and onode
    # to aggregated node in the edges list
    aggcons = extract(arbitrator, arbitrator, (ok, res))
    agg = Node(name="Agg", needs=None, provs=[(Cons("Agg", aggcons),)])

    # nodes outside of the aggregated group
    client = Node(name="Client", needs=None, provs=None)
    cart = Node(name="Cart", needs=None, provs=None)

    nodes = [agg, client, cart, shop]
    edges = [
        Edge(src=client, dst=cart, cons=None),
        Edge(src=client, dst=shop, cons=None),
        Edge(src=client, dst=agg, cons=None),
        # even after aggregation, cross edges must be added explicitly
        Edge(src=agg, dst=shop, cons=None),
    ]

    g = graph(nodes, edges)
    ok, res = composable(g, client)
    assert ok
    assert len(res.nodes) == 4
    assert len(res.edges) == 4

    # import matplotlib.pyplot as plt
    # from consistency.common import plot
    # plot(g)
    # plt.show()
