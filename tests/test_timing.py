import time

from consistency.common import (
    Cons,
    Edge,
    Node,
    cleanup,
    composable,
    compose,
    graph,
)
from consistency.model.causal_consistency import CausalConsistency
from consistency.model.eventual_consistency import EventualConsistency
from consistency.model.linearizability import Linearizability
from consistency.model.monotonic_reads import MonotonicReads
from consistency.model.monotonic_writes import MonotonicWrites
from consistency.model.pram_consistency import PRAMConsistency
from consistency.model.read_your_writes import ReadYourWrites
from consistency.model.writes_follow_reads import WritesFollowReads

# NOTE: the best way is to go with the following but add a filter
# to remove combinititions that conceptually do not make sense
# ranked: list[tuple[int, tuple[type, ...]]] = [
#     (0, (EventualConsistency,)),
#     (1, (MonotonicReads,)),
#     (1, (MonotonicWrites,)),
#     (1, (ReadYourWrites,)),
#     (1, (WritesFollowReads,)),
#     (3, (PRAMConsistency,)),
#     (4, (CausalConsistency,)),
#     (5, (Linearizability,)),
# ]
# result = []
# for r in range(1, len(ranked) + 1):
#     for combo in combinations(ranked, r):
#         total = sum(item[0] for item in combo)
#         models = tuple(model for item in combo for model in item[1])
#         result.append((total, models))
# result.sort(key=lambda x: x[0])
# now we'll just hardcode the result
result: list[tuple[int, tuple[type, ...]]] = [
    # score 0: EC
    (0, (EventualConsistency,)),
    # score 1: individual session guarantees
    (1, (MonotonicReads,)),
    (1, (ReadYourWrites,)),
    (1, (MonotonicWrites,)),
    (1, (WritesFollowReads,)),
    # score 2: pairwise combinations
    (2, (MonotonicReads, ReadYourWrites)),
    (2, (MonotonicReads, MonotonicWrites)),
    (2, (MonotonicReads, WritesFollowReads)),
    (2, (ReadYourWrites, MonotonicWrites)),
    (2, (ReadYourWrites, WritesFollowReads)),
    (2, (MonotonicWrites, WritesFollowReads)),
    # score 3: 3-way combinations
    # (3, (MonotonicReads, ReadYourWrites, MonotonicWrites)), # PRAM
    (3, (PRAMConsistency,)),
    (3, (MonotonicReads, ReadYourWrites, WritesFollowReads)),
    (3, (MonotonicReads, MonotonicWrites, WritesFollowReads)),
    (3, (ReadYourWrites, MonotonicWrites, WritesFollowReads)),
    # score 4: all 4 session guarantees (causal)
    # (4, (MonotonicReads, ReadYourWrites, MonotonicWrites, WritesFollowReads)),
    (4, (CausalConsistency,)),
    # score 5: linearizability
    (5, (Linearizability,)),
]

@cleanup
def test_entry() -> None:
    print(result)


@cleanup
def test_timing_simple() -> None:
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

    client = Node(name="Client", needs=None, provs=None)
    cart = Node(name="Cart", needs=None, provs=None)

    nodes.extend([client, cart])
    edges.extend(
        [
            Edge(src=client, dst=cart, cons=None),
            Edge(src=client, dst=shop, cons=None),
            Edge(src=client, dst=arbitrator, cons=None),
        ]
    )

    g = graph(nodes, edges)
    time.perf_counter()
    ok, res = composable(g, client)
    time.perf_counter()
    assert ok
