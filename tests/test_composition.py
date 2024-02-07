import z3

from consistency.common import compatible, compose
from consistency.model.monotonic_reads import MonotonicReads
from consistency.model.monotonic_writes import MonotonicWrites
from consistency.model.pram_consistency import PRAMConsistency
from consistency.model.read_your_writes import ReadYourWrites
from consistency.model.writes_follow_reads import WritesFollowReads
from consistency.operation import Operation as Op

# composition
# from the paper:
# > "As proved by Brzezinski et al. [2003], PRAM consistency is ensured iff the system provides read-your-write, monotonic reads and monotonic writes guarantee"
# meaning `compatible(pram, {ryw, mr, mw}) == True`
composed = compose(ReadYourWrites.assertions(), MonotonicReads.assertions(), MonotonicWrites.assertions())


def test_known_compatible() -> None:
    assert compatible(PRAMConsistency.assertions(), composed)


def test_known_incompatible() -> None:
    assert not compatible(composed, PRAMConsistency.assertions())


def test_simple_online_shop() -> None:
    """
    a online shop is selling products
    the shop maintains a inventory for each product

    customers can buy products
    each customer maintains a shopping cart (a local copy and replicated with a remote storage system)
    customers can read the shopping cart and write to the shopping cart

    there's a separate transaction log that records all purchases
    when a customer places an order (send a write request with it's local shopping cart)
    the shop will check the inventory
    if the inventory is sufficient, the shop will send a write request to the transaction log (assuming the tx log system will handle payment and delivery)
    when the inventory becomes 0, customers can no longer shop the product
    """
    models = [
        MonotonicReads,
        MonotonicWrites,
        PRAMConsistency,
        ReadYourWrites,
        WritesFollowReads,
    ]

    _, (rd, wr) = Op.Sort()
    op = Op.Create()

    # clients to shopping cart (need to see their own writes):
    # - client reads shopping cart
    # - client writes shopping cart
    # - client writes shop
    client_op = z3.Datatype("ClientOp")
    client_op.declare("crc", ("op", op))
    client_op.declare("cwc", ("op", op))
    client_op.declare("cws", ("op", op))
    client_op = client_op.create()

    client = z3.Const("client", client_op)
    client_constraints = [
        z3.ForAll([client], z3.Implies(client_op.op(client) == client_op.crc, op.type(client_op.op(client)) == rd))
        # z3.ForAll([client], z3.Implies(client_op.op(client) == client_op.cwc, op.type(client_op.op(client)) == wr)),
        # z3.ForAll([client], z3.Implies(client_op.op(client) == client_op.cws, op.type(client_op.op(client)) == wr)),
    ]

    # shop:
    # - shop reads inventory
    # - shop writes inventory
    # - shop writes transaction log
    # - shop reads transaction log
    shop_op = z3.Datatype("ShopOp")
    shop_op.declare("sri", ("op", op))
    shop_op.declare("swi", ("op", op))
    shop_op.declare("swt", ("op", op))
    shop_op.declare("srt", ("op", op))
    shop_op = shop_op.create()

    z3.Const("shop", shop_op)
    shop_constraints = []

    # entity constraints
    entity_constraints = [
        client_constraints,
        shop_constraints,
    ]

    # check individual constraints
    for m in models:
        for c in entity_constraints:
            compatible(m.assertions(), c)

    # assert all available constraints on top of base constraints in turn
    ...
