import time
from itertools import product

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
# choices = []
# for r in range(1, len(ranked) + 1):
#     for combo in combinations(ranked, r):
#         total = sum(item[0] for item in combo)
#         models = tuple(model for item in combo for model in item[1])
#         choices.append((total, models))
# choices.sort(key=lambda x: x[0])
# now we'll just hardcode the choices
choices: list[tuple[int, tuple[type, ...]]] = [
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


def get_assertions(models: tuple[type, ...]) -> list[z3.AstRef]:
    if len(models) == 1:
        return models[0].assertions()

    result = models[0].assertions()
    for model in models[1:]:
        result = compose(result, model.assertions())
    return result # type: ignore[return-value]


@cleanup
def test_timing_shop() -> None:
    results = []

    for arb_choice, tx_choice, shop_choice in product(choices, repeat=3):
        arb_score, arb_models = arb_choice
        tx_score, tx_models = tx_choice
        shop_score, shop_models = shop_choice

        client = Node(name="Client", needs=None, provs=None)
        cart = Node(name="Cart", needs=None, provs=None)
        arbitrator = Node(
            name="Arbitrator",
            needs=None,
            provs=[(Cons("ARB", get_assertions(arb_models)),)], # type: ignore[call-arg]
        )
        tx = Node(
            name="Tx",
            needs=None,
            provs=[(Cons("TX", get_assertions(tx_models)),)] # type: ignore[call-arg]
        )
        shop = Node(
            name="Shop",
            needs=None,
            provs=[(Cons("SHOP", get_assertions(shop_models)),)], # type: ignore[call-arg]
        )

        nodes = [arbitrator, tx, shop, client, cart]
        edges = [
            Edge(src=arbitrator, dst=shop, cons=None),
            Edge(src=arbitrator, dst=tx, cons=None),
            Edge(src=client, dst=cart, cons=None),
            Edge(src=client, dst=shop, cons=None),
            Edge(src=client, dst=arbitrator, cons=None),
        ]

        g = graph(nodes, edges)

        start_time = time.perf_counter()
        ok, res = composable(g, client)
        end_time = time.perf_counter()

        duration = end_time - start_time
        total_score = arb_score + tx_score + shop_score

        result = {
            'composable': ok,
            'duration': duration,
            'total_score': total_score,
            'arbitrator': (arb_score, arb_models),
            'tx': (tx_score, tx_models),
            'shop': (shop_score, shop_models),
        }
        print(result)
        results.append(result)

    results.sort(key=lambda x: (x['total_score'], x['duration']))

    print(f"Total combinations: {len(results)}")
    for result in results:
        print(f"Score: {result['total_score']}, "
              f"Composable: {result['composable']}, "
              f"Duration: {result['duration']:.6f}s, "
              f"Config: ARB={result['arbitrator'][1]}, "
              f"TX={result['tx'][1]}, "
              f"SHOP={result['shop'][1]}")


def test_timing_media() -> None:
    ...


def test_timing_xcom() -> None:
    ...
