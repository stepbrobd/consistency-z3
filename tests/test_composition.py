import itertools

import z3

from consistency.abstract_execution import AbstractExecution as AE
from consistency.common import compatible, compose
from consistency.history import History as H
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

    H.Relation.returns_before()
    H.Relation.same_session()
    so = H.Relation.session_order()
    vis = AE.Relation.visibility()
    AE.Relation.arbitration()

    # client:
    # - client reads shopping cart
    # - client writes shopping cart
    # - client writes shop
    # cart:
    # - cart write client
    # shop:
    # - shop reads inventory
    # - shop writes inventory
    # - shop writes transaction log
    # - shop reads transaction log

    # client:
    client_op_type, (crc, cwc, cws) = z3.EnumSort("ClientOpType", ["crc", "cwc", "cws"])
    client_op = z3.Datatype("ClientOp")
    client_op.declare("cons",
        ("type", client_op_type),
        ("op", op),
    )
    client_op = client_op.create()
    cop = z3.Const("cop", client_op)
    cop_a, cop_b = z3.Consts("cop_a cop_b", client_op)
    cop_constraints = [
        # base constraints
        z3.Implies(client_op.type(cop) == crc, op.type(client_op.op(cop)) == rd),
        z3.Implies(client_op.type(cop) == cwc, op.type(client_op.op(cop)) == wr),
        z3.Implies(client_op.type(cop) == cws, op.type(client_op.op(cop)) == wr),
    ]

    # cart
    cart_op_type, (kwc, ) = z3.EnumSort("CartOpType", ["kwc"])
    cart_op = z3.Datatype("CartOp")
    cart_op.declare("cons",
        ("type", cart_op_type),
        ("op", op),
    )
    cart_op = cart_op.create()
    kop = z3.Const("kop", cart_op)
    kop_a, kop_b = z3.Consts("kop_a kop_b", cart_op)
    kop_constraints = [
        # base constraints
        z3.Implies(cart_op.type(kop) == kwc, op.type(cart_op.op(kop)) == wr),
    ]

    # shop
    shop_op_type, (sri, swi, swt, srt) = z3.EnumSort("ShopOpType", ["sri", "swi", "swt", "srt"])
    shop_op = z3.Datatype("ShopOp")
    shop_op.declare("cons",
        ("type", shop_op_type),
        ("op", op),
    )
    shop_op = shop_op.create()

    sop = z3.Const("sop", shop_op)
    sop_a, sop_b = z3.Consts("sop_a sop_b", shop_op)
    sop_constraints = [
        # base constraints
        z3.Implies(shop_op.type(sop) == sri, op.type(shop_op.op(sop)) == rd),
        z3.Implies(shop_op.type(sop) == swi, op.type(shop_op.op(sop)) == wr),
        z3.Implies(shop_op.type(sop) == swt, op.type(shop_op.op(sop)) == wr),
        z3.Implies(shop_op.type(sop) == srt, op.type(shop_op.op(sop)) == rd),
    ]

    # check individual constraints
    for c in [cop_constraints, kop_constraints, sop_constraints]:
        s = z3.Solver()
        s.add(c)
        assert s.check() == z3.sat
        for m in models:
            s.push()
            s.add(m.assertions())
            assert s.check() == z3.sat
            s.pop()

    # cross dependencies
    deps = [
        # client -> cart
        # a rd crc guarantees a subsequent wr kwc
        z3.Implies(z3.And(client_op.type(cop_a) == crc, cart_op.type(kop_b) == kwc, vis(client_op.op(cop_a), cart_op.op(kop_b))), so(client_op.op(cop_a), cart_op.op(kop_b))),
        # a wr cwc guarantees a subsequent wr kwc
        z3.Implies(z3.And(client_op.type(cop_a) == cwc, cart_op.type(kop_b) == kwc, vis(client_op.op(cop_a), cart_op.op(kop_b))), so(client_op.op(cop_a), cart_op.op(kop_b))),
        # cart -> client
        # a wr kwc guarantees all subsequent read of carts to be visible
        z3.Implies(z3.And(cart_op.type(kop_a) == kwc, client_op.type(cop_b) == crc, vis(cart_op.op(kop_a), client_op.op(cop_b))), vis(cart_op.op(kop_a), client_op.op(cop_b))),
        # shop -> cart
    ]

    # sanity check
    s = z3.Solver()
    s.add(cop_constraints + kop_constraints + sop_constraints + deps)
    assert s.check() == z3.sat

    # assert all available constraints on top of base constraints in turn
    # compatible(m.assertions(), c)
    # itertools generate combinations for clients, carts, shops
    all = compose(*cop_constraints, *kop_constraints, *sop_constraints, *deps)
    for cm, km, sm in itertools.product(models, repeat=3):
        print(f"client: {cm.__name__}; cart: {km.__name__}; shop: {sm.__name__}")
        for a, b in itertools.permutations([cm, km, sm], 2):
            print(f"  {a.__name__} <- {b.__name__}")
            # assert compatible(a.assertions(), b.assertions(), others=all)
            compatible(a.assertions(), b.assertions(), others=all)
