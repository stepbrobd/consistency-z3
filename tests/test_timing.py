import csv
import tempfile
import time
from collections import Counter
from collections.abc import Callable
from itertools import product
from pathlib import Path

import pytest
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


# @pytest.mark.slow
@cleanup
def test_timing_shop() -> None:
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

    temp_dir = Path(tempfile.mkdtemp())
    csv_file = temp_dir / "shop_timing_results.csv"
    print(f"saving results to: {csv_file}")
    with open(csv_file, "w", newline="") as f:
        writer = csv.writer(f)
        writer.writerow(
            [
                "composable",
                "duration",
                "score",
                "arbitrator_score",
                "arbitrator_name",
                "tx_score",
                "tx_name",
                "shop_score",
                "shop_name",
            ]
        )

    results = []

    for arb_choice, tx_choice, shop_choice in list(
        sorted(
            product(choices, repeat=3),
            key=lambda x: (x[0][0] + x[1][0] + x[2][0]),
        )
    ):
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
            writer.writerow(
                [
                    ok,
                    duration,
                    score,
                    arb_score,
                    get_name(arb_choice),
                    tx_score,
                    get_name(tx_choice),
                    shop_score,
                    get_name(shop_choice),
                ]
            )

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


@pytest.mark.slow
@cleanup
def test_timing_xc() -> None:
    temp_dir = Path(tempfile.mkdtemp())
    csv_file = temp_dir / "xc_timing_results.csv"
    print(f"saving results to: {csv_file}")
    with open(csv_file, "w", newline="") as f:
        writer = csv.writer(f)
        writer.writerow(
            [
                "composable",
                "duration",
                "score",
                "svc1_score",
                "svc1_name",
                "svc2_score",
                "svc2_name",
                "svc3_score",
                "svc3_name",
                "svc4_score",
                "svc4_name",
            ]
        )

    def gensym(name: str) -> Callable[[str, list[str]], list[str]]:
        return lambda s, symbols: [f"{name}_{s}_{symbol}" for symbol in symbols]

    semantics = {
        "mr": (
            MonotonicReads.assertions,
            lambda s: gensym("mr")(s, ["a", "b", "c", "x"]),
        ),
        "mw": (MonotonicWrites.assertions, lambda s: gensym("mw")(s, ["a", "b", "c"])),
        "ryw": (
            ReadYourWrites.assertions,
            lambda s: gensym("ryw")(s, ["a", "b", "c", "x"]),
        ),
        "wfr": (
            WritesFollowReads.assertions,
            lambda s: gensym("wfr")(s, ["a", "b", "c", "x"]),
        ),
    }

    def assertion_for(name: str, sys: str) -> z3.BoolRef:
        assertion_func, symbol_gen = semantics[name]
        return assertion_func(symbol_gen(sys))

    svc_choices = [
        (0, "EventualConsistency"),
        (1, "MonotonicReads"),
        (1, "ReadYourWrites"),
        (1, "MonotonicWrites"),
        (1, "WritesFollowReads"),
        (2, "MonotonicReads + ReadYourWrites"),
        (2, "MonotonicReads + MonotonicWrites"),
        (2, "MonotonicReads + WritesFollowReads"),
        (2, "ReadYourWrites + MonotonicWrites"),
        (2, "ReadYourWrites + WritesFollowReads"),
        (2, "MonotonicWrites + WritesFollowReads"),
        (3, "PRAMConsistency"),
        (3, "MonotonicReads + ReadYourWrites + WritesFollowReads"),
        (3, "MonotonicReads + MonotonicWrites + WritesFollowReads"),
        (3, "ReadYourWrites + MonotonicWrites + WritesFollowReads"),
        (4, "CausalConsistency"),
        (5, "Linearizability"),
    ]

    def get_svc_assertions(choice_name: str, counter_val: int) -> z3.BoolRef:
        if choice_name == "EventualConsistency":
            return z3.BoolVal(True)
        elif choice_name == "MonotonicReads":
            return assertion_for("mr", str(counter_val))
        elif choice_name == "ReadYourWrites":
            return assertion_for("ryw", str(counter_val))
        elif choice_name == "MonotonicWrites":
            return assertion_for("mw", str(counter_val))
        elif choice_name == "WritesFollowReads":
            return assertion_for("wfr", str(counter_val))
        elif choice_name == "PRAMConsistency":
            return compose(
                assertion_for("mr", str(counter_val)),
                assertion_for("ryw", str(counter_val)),
                assertion_for("mw", str(counter_val)),
            )
        elif choice_name == "CausalConsistency":
            return compose(
                assertion_for("mr", str(counter_val)),
                assertion_for("ryw", str(counter_val)),
                assertion_for("mw", str(counter_val)),
                assertion_for("wfr", str(counter_val)),
            )
        elif choice_name == "Linearizability":
            return Linearizability.assertions()
        else:
            parts = choice_name.split(" + ")
            assertions = []
            for part in parts:
                if part == "MonotonicReads":
                    assertions.append(assertion_for("mr", str(counter_val)))
                elif part == "ReadYourWrites":
                    assertions.append(assertion_for("ryw", str(counter_val)))
                elif part == "MonotonicWrites":
                    assertions.append(assertion_for("mw", str(counter_val)))
                elif part == "WritesFollowReads":
                    assertions.append(assertion_for("wfr", str(counter_val)))
            return compose(*assertions)

    results = []

    for svc1_choice, svc2_choice, svc3_choice, svc4_choice in list(
        sorted(
            product(svc_choices, repeat=4),
            key=lambda x: (x[0][0] + x[1][0] + x[2][0] + x[3][0]),
        )
    ):
        Relation.Reset()
        z3.reset_params()
        start_time = time.perf_counter()

        svc1_score, svc1_name = svc1_choice
        svc2_score, svc2_name = svc2_choice
        svc3_score, svc3_name = svc3_choice
        svc4_score, svc4_name = svc4_choice

        counter = Counter(semantics.keys())

        svc1 = Node(
            name="SVC1",
            needs=None,
            provs=[(Cons("SVC1", get_svc_assertions(svc1_name, counter["mr"])),)],
        )
        counter["mr"] += 1

        # SVC1 -> SVC2
        edge1_constraints = [
            assertion_for("mr", str(counter["mr"])),
            assertion_for("ryw", str(counter["ryw"])),
            assertion_for("wfr", str(counter["wfr"])),
        ]
        counter["mr"] += 1
        counter["ryw"] += 1
        counter["wfr"] += 1

        svc2 = Node(
            name="SVC2",
            needs=None,
            provs=[(Cons("SVC2", get_svc_assertions(svc2_name, counter["mw"])),)],
        )
        counter["mw"] += 1

        edge1 = Edge(
            src=svc1,
            dst=svc2,
            cons=[(Cons("EC1", compose(*edge1_constraints)),)],
        )

        # SVC2 -> SVC3
        edge2_constraints = [
            assertion_for("mr", str(counter["mr"])),
            assertion_for("mw", str(counter["mw"])),
            assertion_for("wfr", str(counter["wfr"])),
        ]
        counter["mr"] += 1
        counter["mw"] += 1
        counter["wfr"] += 1

        svc3 = Node(
            name="SVC3",
            needs=None,
            provs=[(Cons("SVC3", get_svc_assertions(svc3_name, counter["ryw"])),)],
        )
        counter["ryw"] += 1

        edge2 = Edge(
            src=svc2,
            dst=svc3,
            cons=[(Cons("EC2", compose(*edge2_constraints)),)],
        )

        # SVC3 -> SVC4
        edge3_constraints = [
            assertion_for("mr", str(counter["mr"])),
            assertion_for("mw", str(counter["mw"])),
            assertion_for("ryw", str(counter["ryw"])),
        ]
        counter["mr"] += 1
        counter["mw"] += 1
        counter["ryw"] += 1

        svc4 = Node(
            name="SVC4",
            needs=None,
            provs=[(Cons("SVC4", get_svc_assertions(svc4_name, counter["wfr"])),)],
        )
        counter["wfr"] += 1

        edge3 = Edge(
            src=svc3,
            dst=svc4,
            cons=[(Cons("EC3", compose(*edge3_constraints)),)],
        )

        # SVC4 -> XC
        edge4_constraints = [
            assertion_for("mr", str(counter["mr"])),
            assertion_for("mw", str(counter["mw"])),
            assertion_for("ryw", str(counter["ryw"])),
        ]
        counter["mr"] += 1
        counter["mw"] += 1
        counter["ryw"] += 1

        xc = Node(
            name="XC",
            needs=None,
            provs=None,
        )

        edge4 = Edge(
            src=svc4,
            dst=xc,
            cons=[(Cons("EC4", compose(*edge4_constraints)),)],
        )

        # full graph
        nodes = [svc1, svc2, svc3, svc4, xc]
        edges = [edge1, edge2, edge3, edge4]

        g = graph(nodes, edges)
        ok, res = composable(g, svc1)

        end_time = time.perf_counter()
        Relation.Reset()
        z3.reset_params()
        duration = end_time - start_time

        score = svc1_score + svc2_score + svc3_score + svc4_score

        with open(csv_file, "a", newline="") as f:
            writer = csv.writer(f)
            writer.writerow(
                [
                    ok,
                    duration,
                    score,
                    svc1_score,
                    svc1_name,
                    svc2_score,
                    svc2_name,
                    svc3_score,
                    svc3_name,
                    svc4_score,
                    svc4_name,
                ]
            )

        result = {
            "composable": ok,
            "duration": duration,
            "score": score,
            "svc1": (svc1_score, svc1_name),
            "svc2": (svc2_score, svc2_name),
            "svc3": (svc3_score, svc3_name),
            "svc4": (svc4_score, svc4_name),
        }
        print(result)
        results.append(result)

    # results.sort(key=lambda x: (x["score"], x["duration"]))
    # print(len(results))
    # print(results)


# NOTE: for this timing test, we decided to move it to future
# work as the number of combinations is too large
# excluding client and admin nodes, there are 9 possible slots
# to plug in the models (17^9 ~ 120 billion)
# even if we only use combinitions with total score of 2
# there will still be 6^9 ~ 10 million combinations
@cleanup
def test_timing_media() -> None: ...
