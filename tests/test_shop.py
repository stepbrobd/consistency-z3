import z3

from consistency.common import composable, Edge, Node
from consistency.model.monotonic_reads import MonotonicReads
from consistency.model.monotonic_writes import MonotonicWrites
from consistency.model.read_your_writes import ReadYourWrites
from consistency.model.writes_follow_reads import WritesFollowReads
from consistency.model.linearizability import Linearizability
from consistency.model.pram_consistency import PRAMConsistency


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
    # usually session guarantees
    layerable = [
        MonotonicReads,
        MonotonicWrites,
        ReadYourWrites,
        WritesFollowReads,
    ]
    # on the two sides of operations
    # if either or both entity(ies) that wish to operate as a single centrualized server
    # session guarantees can be applied, even if one side cannot be precived as a storae system
    # operations between the two entities are considered to be in a "session"
    # session guarantees must apply to all operations in a session (bidirectional arrow)
    # for semantics that are not session guarantees
    # they apply to one signle type of operation (unidirectional arrow)

    nonlayerable = [
        Linearizability,
        PRAMConsistency,
    ]

    client = Node("Client", layerable, (0, len(layerable)), set([]), (0, 0))
    cart = Node("Cart", layerable, (0, len(layerable)), nonlayerable, (1, 1))
    shop = Node("Shop", layerable, (0, len(layerable)), nonlayerable, (1, 1))
    arbitrator = Node("Arbitrator", set([]), (0, 0), set([Linearizability]), (1, 1))
    tx = Node("Tx", layerable, len(layerable), nonlayerable, (1, 1))

    nodes = [client, cart, shop, arbitrator, tx]

    edges = [
        Edge(client, [cart, shop], z3.And()),
        Edge(cart, [client], z3.And()),
        Edge(shop, [client, arbitrator], z3.And()),
        Edge(arbitrator, [shop, tx], z3.And()),
        Edge(tx, [arbitrator], z3.And()),
    ]

    ok, _ = composable(nodes, edges)

    assert ok
