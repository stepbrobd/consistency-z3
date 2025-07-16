import csv
import signal
import tempfile
import time
from collections import Counter
from collections.abc import Callable
from itertools import product
from pathlib import Path
from types import FrameType

import pytest
import z3

from consistency.abstract_execution import AbstractExecution as AE
from consistency.common import (
    Cons,
    Edge,
    Node,
    cleanup,
    composable,
    compose,
    graph,
)
from consistency.history import History as H
from consistency.model.causal_consistency import CausalConsistency
from consistency.model.eventual_consistency import EventualConsistency
from consistency.model.linearizability import Linearizability
from consistency.model.monotonic_reads import MonotonicReads
from consistency.model.monotonic_writes import MonotonicWrites
from consistency.model.pram_consistency import PRAMConsistency
from consistency.model.read_your_writes import ReadYourWrites
from consistency.model.writes_follow_reads import WritesFollowReads
from consistency.operation import Operation as Op
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
    class Timeout(Exception):
        pass

    def handler(signal: int, frame: FrameType | None) -> None:
        raise Timeout("z3 timed out")

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

        signal.signal(signal.SIGALRM, handler)
        signal.alarm(10)

        start_time = time.perf_counter()

        svc1_score, svc1_name = svc1_choice
        svc2_score, svc2_name = svc2_choice
        svc3_score, svc3_name = svc3_choice
        svc4_score, svc4_name = svc4_choice

        try:
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
            ok, _ = composable(g, svc1)

            end_time = time.perf_counter()
            duration = end_time - start_time
        except Timeout:
            ok, duration = False, 10.0
        finally:
            signal.alarm(0)
            Relation.Reset()
            z3.reset_params()

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


@pytest.mark.slow
@cleanup
def test_timing_media() -> None:
    class Timeout(Exception):
        pass

    def handler(signal: int, frame: FrameType | None) -> None:
        raise Timeout("z3 timed out")

    temp_dir = Path(tempfile.mkdtemp())
    csv_file = temp_dir / "media_timing_results.csv"
    print(f"saving results to: {csv_file}")
    with open(csv_file, "w", newline="") as f:
        writer = csv.writer(f)
        writer.writerow(
            [
                "composable",
                "duration",
                "score",
                "user_db_score",
                "user_db_name",
                "metadata_db_score",
                "metadata_db_name",
                "rent_db_score",
                "rent_db_name",
                "review_db_score",
                "review_db_name",
                "video_db_score",
                "video_db_name",
            ]
        )

    db_choices = [
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

    def get_db_assertions(choice_name: str) -> z3.BoolRef:
        assertions = []
        if choice_name == "EventualConsistency":
            assertions.append(EventualConsistency.assertions())
        elif choice_name == "MonotonicReads":
            assertions.append(MonotonicReads.assertions())
        elif choice_name == "ReadYourWrites":
            assertions.append(ReadYourWrites.assertions())
        elif choice_name == "MonotonicWrites":
            assertions.append(MonotonicWrites.assertions())
        elif choice_name == "WritesFollowReads":
            assertions.append(WritesFollowReads.assertions())
        elif choice_name == "PRAMConsistency":
            assertions.append(
                compose(
                    MonotonicReads.assertions(),
                    ReadYourWrites.assertions(),
                    MonotonicWrites.assertions(),
                )
            )
        elif choice_name == "CausalConsistency":
            assertions.append(
                compose(
                    MonotonicReads.assertions(),
                    ReadYourWrites.assertions(),
                    MonotonicWrites.assertions(),
                    WritesFollowReads.assertions(),
                )
            )
        elif choice_name == "Linearizability":
            assertions.append(Linearizability.assertions())
        else:
            parts = choice_name.split(" + ")
            for part in parts:
                if part == "MonotonicReads":
                    assertions.append(MonotonicReads.assertions())
                elif part == "ReadYourWrites":
                    assertions.append(ReadYourWrites.assertions())
                elif part == "MonotonicWrites":
                    assertions.append(MonotonicWrites.assertions())
                elif part == "WritesFollowReads":
                    assertions.append(WritesFollowReads.assertions())
        return compose(*assertions)

    for (
        user_db_choice,
        metadata_db_choice,
        rent_db_choice,
        review_db_choice,
        video_db_choice,
    ) in list(
        sorted(
            product(db_choices, repeat=5),
            key=lambda x: (x[0][0] + x[1][0] + x[2][0] + x[3][0] + x[4][0]),
        )
    ):
        Relation.Reset()
        z3.reset_params()

        signal.signal(signal.SIGALRM, handler)
        signal.alarm(10)

        start_time = time.perf_counter()

        user_db_score, user_db_name = user_db_choice
        metadata_db_score, metadata_db_name = metadata_db_choice
        rent_db_score, rent_db_name = rent_db_choice
        review_db_score, review_db_name = review_db_choice
        video_db_score, video_db_name = video_db_choice

        try:
            # predicates
            _, (rd, wr) = Op.Sort()
            op = Op.Create()
            ob = H.Relation.same_object()
            rb = H.Relation.returns_before()
            vis = AE.Relation.visibility()

            # nodes
            admin = Node(name="Admin", needs=None, provs=None)
            client = Node(name="Client", needs=None, provs=None)
            login = Node(
                name="Login",
                needs=[
                    (
                        Cons(
                            "MW + WFR",
                            compose(
                                MonotonicWrites.assertions(),
                                WritesFollowReads.assertions(),
                            ),
                        ),
                    )
                ],
                provs=None,
            )
            rent = Node(
                name="Rent",
                needs=[(Cons("MR", MonotonicReads.assertions()),)],
                provs=None,
            )
            review = Node(
                name="Review",
                needs=[(Cons("RYW", ReadYourWrites.assertions()),)],
                provs=None,
            )
            review = Node(
                name="Review",
                needs=[(Cons("RYW", ReadYourWrites.assertions()),)],
                provs=None,
            )  # match whatever review db provides
            video = Node(
                name="Video",
                needs=[(Cons("MR", MonotonicReads.assertions()),)],
                provs=None,
            )  # video node's action depends on the read output of the metadata db
            user_db = Node(
                name="User DB",
                needs=None,
                provs=[(Cons("USER_DB", get_db_assertions(user_db_name)),)],
            )
            metadata_db = Node(
                name="Metadata DB",
                needs=None,
                provs=[(Cons("METADATA_DB", get_db_assertions(metadata_db_name)),)],
            )
            rent_db = Node(
                name="Rent DB",
                needs=None,
                provs=[(Cons("RENT_DB", get_db_assertions(rent_db_name)),)],
            )

            review_db = Node(
                name="Review DB",
                needs=None,
                provs=[(Cons("REVIEW_DB", get_db_assertions(review_db_name)),)],
            )

            video_db = Node(
                name="Video DB",
                needs=None,
                provs=[(Cons("VIDEO_DB", get_db_assertions(video_db_name)),)],
            )

            # operations
            op_client_register = Op.Const("Op Client Register")
            op_client_login = Op.Const("Op Client Login")
            op_admin_login = Op.Const("Op Admin Login")
            op_admin_modify = Op.Const("Op Admin Modify")
            op_user_db_rd = Op.Const("Op User DB Read")
            op_user_db_wr = Op.Const("Op User DB Write")
            op_client_rent_video = Op.Const("Op Client Rent Video")
            op_rent_check_metadata = Op.Const("Op Rent Check Metadata")
            op_client_watch_video = Op.Const("Op Client Watch Video")
            op_video_check_metadata = Op.Const("Op Video Check Metadata")
            op_review_check_metadata = Op.Const("Op Review Check Metadata")
            op_client_read_review = Op.Const("Op Client Read Review")
            op_client_write_review = Op.Const("Op Client Write Review")
            op_admin_write_metadata = Op.Const("Op Admin Write Metadata")
            op_admin_write_video = Op.Const("Op Admin Write Video")

            # premise
            cons_op_types = z3.And(
                op.type(op_client_register) == wr,  # type: ignore
                op.type(op_client_login) == rd,  # type: ignore
                op.type(op_admin_login) == rd,  # type: ignore
                op.type(op_admin_modify) == wr,  # type: ignore
                op.type(op_user_db_rd) == rd,  # type: ignore
                op.type(op_user_db_wr) == wr,  # type: ignore
                op.type(op_client_rent_video) == wr,  # type: ignore
                op.type(op_video_check_metadata) == rd,  # type: ignore
                op.type(op_rent_check_metadata) == rd,  # type: ignore
                op.type(op_review_check_metadata) == rd,  # type: ignore
                op.type(op_client_read_review) == rd,  # type: ignore
                op.type(op_client_write_review) == wr,  # type: ignore
                op.type(op_client_watch_video) == rd,  # type: ignore
                op.type(op_admin_write_metadata) == wr,  # type: ignore
                op.type(op_admin_write_video) == wr,  # type: ignore
            )

            # edge constraints
            ec_common_login = z3.And(
                rb(op_client_login, op_client_read_review),
                rb(op_client_login, op_client_rent_video),
                rb(op_client_login, op_client_write_review),
                rb(op_client_login, op_client_watch_video),
            )
            ec_common_admin = z3.And(
                rb(op_admin_login, op_admin_modify),
                rb(op_admin_login, op_admin_write_metadata),
                rb(op_admin_login, op_admin_write_video),
            )

            ec_client_wr_login = None  # no constraints for registration
            ec_client_rd_login = [
                (
                    Cons(
                        "User must register before login",
                        z3.And(  # type: ignore
                            ec_common_login,
                            z3.Exists(
                                [op_client_login, op_client_register],
                                z3.And(
                                    ob(op_client_login, op_client_register),
                                    vis(op_client_register, op_client_login),
                                ),
                            ),
                        ),
                    ),
                )
            ]
            ec_admin_rd_login = (
                None  # admins are pre-registered, no need to assign constraints here
            )
            # admin writes require a previous admin login
            ec_admin_wr_login = [
                (Cons("Admin writes requires login", ec_common_admin),)  # type: ignore
            ]
            # user db reads require a previous write, admin writes must reflect on user reads
            ec_login_rd_user_db = [
                (
                    Cons(
                        "Combined constraints from users and admins",
                        z3.And(  # type: ignore
                            z3.Exists(
                                [op_user_db_rd, op_user_db_wr],
                                z3.And(
                                    ob(op_user_db_rd, op_user_db_wr),
                                    vis(op_user_db_wr, op_user_db_rd),
                                ),
                            ),
                            z3.Exists(
                                [op_user_db_rd, op_admin_modify],
                                z3.And(
                                    ob(op_admin_modify, op_user_db_rd),
                                    vis(op_admin_modify, op_user_db_rd),
                                ),
                            ),
                        ),
                    ),
                )
            ]
            ec_login_wr_user_db = None  # assume all user db writes are valid

            ec_client_wr_rent = [
                (Cons("Client login before rent movie", ec_common_login),)  # type: ignore
            ]
            ec_rent_rd_metadata_db = [
                (
                    Cons(
                        "Client login before rent movie",
                        z3.Exists(
                            [op_client_rent_video, op_rent_check_metadata],
                            z3.And(
                                ob(op_client_rent_video, op_rent_check_metadata),
                                rb(op_rent_check_metadata, op_client_rent_video),
                            ),
                        ),
                    ),
                )
            ]  # Q: replace rb with so? A: rb only. return after the rent service reads the metadata
            ec_rent_wr_rent_db = None  # assume all rent db writes are valid

            ec_client_rd_review = [
                (Cons("Require login before read review", ec_common_login),)  # type: ignore
            ]
            ec_client_wr_review = [
                (Cons("Require login before write review", ec_common_login),)  # type: ignore
            ]
            ec_review_rd_metadata_db = [
                (
                    Cons(
                        "Check metadata before read review",
                        z3.Exists(
                            [op_client_read_review, op_review_check_metadata],
                            z3.And(
                                ob(op_client_read_review, op_review_check_metadata),
                                rb(op_review_check_metadata, op_client_read_review),
                            ),
                        ),
                    ),
                )
            ]  # see above about rb/so return after the review service reads the metadata
            ec_review_rd_review_db = [
                (
                    Cons(
                        "Match review read metadata constraints",
                        ec_review_rd_metadata_db[0][0].cons,
                    ),
                )
            ]
            ec_review_wr_review_db = None  # assume all review db writes are valid

            ec_client_rd_video = [(Cons("Client watch video", ec_common_login),)]  # type: ignore
            ec_video_rd_metadata_db = [
                (
                    Cons(
                        "Check metadata before watch video",
                        z3.Exists(
                            [op_client_watch_video, op_video_check_metadata],
                            z3.And(
                                ob(op_client_watch_video, op_video_check_metadata),
                                rb(op_video_check_metadata, op_client_watch_video),
                            ),
                        ),
                    ),
                )
            ]  # see above for rb so. return after the video service reads the metadata
            ec_video_rd_video_db = [
                (
                    Cons(
                        "Match video read metadata constraints",
                        ec_video_rd_metadata_db[0][0].cons,
                    ),
                )
            ]

            ec_admin_wr_metadata_db = [
                (Cons("Admin login before write metadata", z3.And(ec_common_admin)),)  # type: ignore
            ]
            ec_admin_wr_video = [
                (Cons("Admin login before update video", z3.And(ec_common_admin)),)  # type: ignore
            ]
            ec_video_wr_video_db = None  # assume all video db writes are valid

            nodes = [
                admin,
                client,
                login,
                user_db,
                metadata_db,
                rent,
                rent_db,
                review,
                review_db,
                video,
                video_db,
            ]

            edges = [
                Edge(client, login, ec_client_wr_login),  # client register
                Edge(client, login, ec_client_rd_login),  # client login
                Edge(admin, login, ec_admin_rd_login),  # admin login
                Edge(admin, login, ec_admin_wr_login),  # admin modify
                Edge(login, user_db, ec_login_rd_user_db),  # user db read
                Edge(login, user_db, ec_login_wr_user_db),  # user db write
                Edge(client, rent, ec_client_wr_rent),  # client rent
                Edge(rent, metadata_db, ec_rent_rd_metadata_db),  # rent read metadata
                Edge(rent, rent_db, ec_rent_wr_rent_db),  # rent db read
                Edge(client, review, ec_client_rd_review),  # client read review
                Edge(client, review, ec_client_wr_review),  # client write review
                Edge(
                    review, metadata_db, ec_review_rd_metadata_db
                ),  # review reads from metadata (check if title exist before rd/wr to review db)
                Edge(review, review_db, ec_review_rd_review_db),  # review db read
                Edge(review, review_db, ec_review_wr_review_db),  # review db write
                Edge(client, video, ec_client_rd_video),  # client watch video
                Edge(
                    video, metadata_db, ec_video_rd_metadata_db
                ),  # checked if a title is valid
                Edge(video, video_db, ec_video_rd_video_db),  # video db read
                Edge(
                    admin, metadata_db, ec_admin_wr_metadata_db
                ),  # admin write metadata
                Edge(admin, video, ec_admin_wr_video),  # admin write video
                Edge(video, video_db, ec_video_wr_video_db),  # video db write
            ]

            g = graph(nodes, edges)
            ok, _res = composable(g, client, cons_op_types)  # type: ignore[arg-type]

            end_time = time.perf_counter()
            duration = end_time - start_time
        except Timeout:
            ok, duration = False, 10.0
        finally:
            signal.alarm(0)
            Relation.Reset()
            z3.reset_params()

        score = (
            user_db_score
            + metadata_db_score
            + rent_db_score
            + review_db_score
            + video_db_score
        )

        with open(csv_file, "a", newline="") as f:
            writer = csv.writer(f)
            writer.writerow(
                [
                    ok,
                    duration,
                    score,
                    user_db_score,
                    user_db_name,
                    metadata_db_score,
                    metadata_db_name,
                    rent_db_score,
                    rent_db_name,
                    review_db_score,
                    review_db_name,
                    video_db_score,
                    video_db_name,
                ]
            )

        result = {
            "composable": ok,
            "duration": duration,
            "score": score,
            "user_db": (user_db_score, user_db_name),
            "metadata_db": (metadata_db_score, metadata_db_name),
            "rent_db": (rent_db_score, rent_db_name),
            "review_db": (review_db_score, review_db_name),
            "video_db": (video_db_score, video_db_name),
        }
        print(result)
