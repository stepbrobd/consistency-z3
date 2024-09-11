import pytest
import z3

from consistency.common import Cons, Edge, Node, composable, powerset
from consistency.model.linearizability import Linearizability
from consistency.model.monotonic_reads import MonotonicReads
from consistency.model.monotonic_writes import MonotonicWrites
from consistency.model.read_your_writes import ReadYourWrites
from consistency.model.writes_follow_reads import WritesFollowReads


@pytest.mark.skip(reason="too slow")
def test_shop() -> None:
    """
    a online shop is selling products
    the shop maintains a inventory for each product

    customers can buy products
    each customer maintains a shopping cart (the local copy is replicated with a remote storage system)
    customers can read the shopping cart and write to the shopping cart

    there's a separate transaction log that records all purchases
    when a customer places an order (send a write request with it's local shopping cart)
    the shop will check the inventory
    if the inventory is sufficient, the shop will send a write request to the transaction log
    assuming the tx log system will handle payment and delivery
    when the inventory becomes 0, customers can no longer shop the product
    """
    # on the two sides of operations
    # if either or both entity(ies) that wish to operate as a single centrualized server
    # session guarantees can be applied, even if one side cannot be precived as a storae system
    # operations between the two entities are considered to be in a "session"
    # session guarantees must apply to all operations in a session (bidirectional arrow, lives on edges)
    # for semantics that are not session guarantees
    # they apply to one signle type of operation (unidirectional arrow)
    sg = list((Cons("N/A", z3.BoolVal(False)),) if x == () else x for x in powerset((
        Cons("MR", MonotonicReads.assertions()),
        Cons("MW", MonotonicWrites.assertions()),
        Cons("RYW", ReadYourWrites.assertions()),
        Cons("WFR", WritesFollowReads.assertions()),
    )))

    # for x in sg: print(f"{x}\n")

    client = Node(name="Client", needs=sg, provs=None)
    cart = Node(name="Cart", needs=None, provs=sg)
    shop = Node(name="Shop", needs=None, provs=sg)
    arbitrator = Node(name="Arbitrator", needs=None, provs=[(Cons("LZ", Linearizability.assertions()),)])
    tx = Node(name="Tx", needs=None, provs=None)

    nodes = [client, cart, shop, arbitrator, tx]

    edges = [
        Edge(src=client, dst=cart, cons=None),
        Edge(src=cart, dst=client, cons=None),

        Edge(src=client, dst=shop, cons=None),
        Edge(src=shop, dst=client, cons=None),

        Edge(src=client, dst=arbitrator, cons=None),
        Edge(src=arbitrator, dst=client, cons=None),

        Edge(src=arbitrator, dst=shop, cons=None),
        Edge(src=arbitrator, dst=tx, cons=None),
    ]

    ok, res = composable(nodes, edges)
    print(f"Possible assignments: {len(res)}")
    assert ok
