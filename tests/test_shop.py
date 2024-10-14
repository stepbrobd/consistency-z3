from consistency.common import (
    Cons,
    Edge,
    Node,
    composable,
    composable_v2,
    compose,
    graph,
)
from consistency.model.linearizability import Linearizability
from consistency.model.monotonic_reads import MonotonicReads
from consistency.model.read_your_writes import ReadYourWrites


# @pytest.mark.skip(reason="too slow")
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

    # all possible combinations of session guarantees
    # sg = list((Cons("N/A", z3.BoolVal(False)),) if x == () else x for x in powerset((
    #     Cons("MR", MonotonicReads.assertions()),
    #     Cons("MW", MonotonicWrites.assertions()),
    #     Cons("RYW", ReadYourWrites.assertions()),
    #     Cons("WFR", WritesFollowReads.assertions()),
    # )))
    # print(len(sg))
    # for x in sg: print(f"{x}\n")

    # ar+->shop
    # +--->tx
    # enforce all requests to shop and tx must go through an arbitrator
    # all write requests to arbitrator guarantees: (client want to make a purchase)
    # 1. arbitrator write to tx (purchase received at arbitrator, arbitrator writes to transaction log)
    # 2. arbitrator read from shop (check inventory)
    # 3. arbitrator write to shop (decrement inventory, or else write nothing, and client should be notified)
    arbitrator = Node(name="Arbitrator", needs=None, provs=[(Cons("LZ", Linearizability.assertions()),)])
    tx = Node(name="Tx", needs=None, provs=[(Cons("LZ", Linearizability.assertions()),)])
    shop = Node(name="Shop", needs=None, provs=[(Cons("RMW+MR", compose(ReadYourWrites.assertions(), MonotonicReads.assertions())),)])

    nodes = [arbitrator, tx, shop]
    edges = [
        Edge(src=arbitrator, dst=shop, cons=None),
        Edge(src=arbitrator, dst=tx, cons=None),
    ]

    ok, res = composable(nodes, edges)
    print(f"Possible assignments: {len(res)}")
    assert ok

    # nodes outside of the arbitrator group
    client = Node(name="Client", needs=None, provs=None)
    cart = Node(name="Cart", needs=None, provs=None)

    nodes.extend([client, cart])
    edges.extend([
        Edge(src=client, dst=cart, cons=None),
        Edge(src=client, dst=shop, cons=None),
        Edge(src=client, dst=arbitrator, cons=None),
    ])

    g = graph(nodes, edges)
    ok, res = composable_v2(g)
    # plot(g)
    # plt.show()
