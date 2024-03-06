from consistency.common import composable, node
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
    if the inventory is sufficient, the shop will send a write request to the transaction log (assuming the tx log system will handle payment and delivery)
    when the inventory becomes 0, customers can no longer shop the product
    """
    # on the two sides of operations
    # if either or both entity(ies) that wish to operate as a single centrualized server
    # session guarantees can be applied, even if one side cannot be precived as a storae system
    # operations between the two entities are considered to be in a "session"
    # session guarantees must apply to all operations in a session (bidirectional arrow)
    # for semantics that are not session guarantees
    # they apply to one signle type of operation (unidirectional arrow)
    semantics = (
        Linearizability,
        PRAMConsistency,
    )

    client = node("client", (), True) # session guarantees
    cart = node("cart", semantics, True) # session guarantees
    shop = node("shop", semantics, True) # session guarantees
    arbitrator = node("arbitrator", (Linearizability,), False) # arbitrator must apply stric total order
    tx = node("tx", semantics, True) # session guarantees

    g = {
        client: {cart, shop},
        cart: {client},
        shop: {client, arbitrator},
        arbitrator: {shop, tx},
        tx: {arbitrator},
    }

    assert composable(g)
