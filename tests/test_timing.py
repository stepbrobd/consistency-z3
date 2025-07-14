import csv
import tempfile
import time
from collections import Counter
from collections.abc import Callable
from itertools import product
from pathlib import Path

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
from consistency.relation import Relation

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
    return result  # type: ignore[return-value]


def get_name(choice: tuple[int, tuple[type, ...]]) -> str:
    _, models = choice
    if len(models) == 1:
        return models[0].__name__
    return " + ".join(model.__name__ for model in models)


@cleanup
def test_timing_shop() -> None:
    temp_dir = Path(tempfile.mkdtemp())
    csv_file = temp_dir / "shop_timing_results.csv"
    print(f"saving results to: {csv_file}")
    with open(csv_file, "w", newline="") as f:
        writer = csv.writer(f)
        writer.writerow(["composable", "duration", "score", "arbitrator_score", "arbitrator_name", "tx_score", "tx_name", "shop_score", "shop_name"])

    results = []

    for arb_choice, tx_choice, shop_choice in product(choices, repeat=3):
        Relation.Reset()
        z3.reset_params()
        start_time = time.perf_counter()

        arb_score, arb_models = arb_choice
        tx_score, tx_models = tx_choice
        shop_score, shop_models = shop_choice

        client = Node(name="Client", needs=None, provs=None)
        cart = Node(name="Cart", needs=None, provs=None)
        arbitrator = Node(
            name="Arbitrator",
            needs=None,
            provs=[(Cons("ARB", get_assertions(arb_models)),)],  # type: ignore[call-arg]
        )
        tx = Node(
            name="Tx",
            needs=None,
            provs=[(Cons("TX", get_assertions(tx_models)),)],  # type: ignore[call-arg]
        )
        shop = Node(
            name="Shop",
            needs=None,
            provs=[(Cons("SHOP", get_assertions(shop_models)),)],  # type: ignore[call-arg]
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
        ok, res = composable(g, client)

        end_time = time.perf_counter()
        Relation.Reset()
        z3.reset_params()
        duration = end_time - start_time

        score = arb_score + tx_score + shop_score

        with open(csv_file, "a", newline="") as f:
            writer = csv.writer(f)
            writer.writerow([
                ok, duration, score,
                arb_score, get_name(arb_choice),
                tx_score, get_name(tx_choice),
                shop_score, get_name(shop_choice)
            ])

        result = {
            "composable": ok,
            "duration": duration,
            "score": score,
            "arbitrator": (arb_score, get_name(arb_choice)),
            "tx": (tx_score, get_name(tx_choice)),
            "shop": (shop_score, get_name(shop_choice)),
        }
        print(result)
        results.append(result)

    # results.sort(key=lambda x: (x["score"], x["duration"]))
    # print(len(results))
    # print(results)


def test_timing_media() -> None:
    ...


def test_timing_xcom() -> None:
    ...
