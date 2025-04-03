from consistency.common import (
    Cons,
    Edge,
    Node,
    cleanup,
    composable,
    compose,
    extract,
    graph,
)
from consistency.model.causal_consistency import CausalConsistency
from consistency.model.monotonic_reads import MonotonicReads
from consistency.model.monotonic_writes import MonotonicWrites
from consistency.model.read_your_writes import ReadYourWrites
from consistency.model.writes_follow_reads import WritesFollowReads


@cleanup
def test_cross_causal() -> None:
    mr = Node(
        name="MR",
        needs=None,
        provs=[(Cons("MR", MonotonicReads.assertions()),)],
    )
    mw = Node(
        name="MW", needs=None, provs=[(Cons("MW", MonotonicWrites.assertions()),)]
    )
    ryw = Node(
        name="RYW",
        needs=None,
        provs=[(Cons("RYW", ReadYourWrites.assertions()),)],
    )
    wfr = Node(
        name="WFR",
        needs=None,
        provs=[(Cons("WFR", WritesFollowReads.assertions()),)],
    )
    svc = Node(
        name="SVC",
        needs=[(Cons("SVC", CausalConsistency.assertions()),)],
        provs=None,
    )

    nodes = [mr, svc]
    edges = [
        Edge(
            src=mr,
            dst=svc,
            cons=[
                (
                    Cons(
                        "EC",
                        compose(
                            MonotonicWrites.assertions(),
                            ReadYourWrites.assertions(),
                            WritesFollowReads.assertions(),
                        ),
                    ),
                )
            ],
        )
    ]

    g = graph(nodes, edges)
    ok, res = composable(g, svc)
    assert ok

    # mr + svc
    mrsvc = Node(
        name="MRSVC",
        needs=[(Cons("SVC", CausalConsistency.assertions()),)],
        provs=[(Cons("MRSVC", extract(svc, svc, (ok, res))),)],
    )

    nodes = [mw, mrsvc]
    edges = [
        Edge(
            src=mw,
            dst=mrsvc,
            cons=[
                (
                    Cons(
                        "EC",
                        compose(
                            MonotonicReads.assertions(),
                            ReadYourWrites.assertions(),
                            WritesFollowReads.assertions(),
                        ),
                    ),
                )
            ],
        )
    ]

    g = graph(nodes, edges)
    ok, res = composable(g, mrsvc)
    assert ok

    # mr + mw + svc
    mrmwsvc = Node(
        name="MRMWSVC",
        needs=[(Cons("SVC", CausalConsistency.assertions()),)],
        provs=[(Cons("MRMWSVC", extract(mrsvc, mrsvc, (ok, res))),)],
    )

    nodes = [ryw, mrmwsvc]
    edges = [
        Edge(
            src=ryw,
            dst=mrsvc,
            cons=[
                (
                    Cons(
                        "EC",
                        compose(
                            MonotonicReads.assertions(),
                            MonotonicWrites.assertions(),
                            WritesFollowReads.assertions(),
                        ),
                    ),
                )
            ],
        )
    ]

    g = graph(nodes, edges)
    ok, res = composable(g, mrmwsvc)
    assert ok

    # mr + mw + wfr + svc
    mrmwwfrsvc = Node(
        name="MRMWWFRSVC",
        needs=[(Cons("SVC", CausalConsistency.assertions()),)],
        provs=[(Cons("MRMWWFRSVC", extract(mrsvc, mrsvc, (ok, res))),)],
    )

    nodes = [wfr, mrmwsvc]
    edges = [
        Edge(
            src=wfr,
            dst=mrmwwfrsvc,
            cons=[
                (
                    Cons(
                        "EC",
                        compose(
                            MonotonicReads.assertions(),
                            MonotonicWrites.assertions(),
                            ReadYourWrites.assertions(),
                        ),
                    ),
                )
            ],
        )
    ]

    g = graph(nodes, edges)
    ok, res = composable(g, mrmwwfrsvc)
    assert ok

    # mrmwwfrsvc is the aggregated node that exposes cross storage system causal
    # to upper layer services
