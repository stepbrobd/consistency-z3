from collections import Counter
from collections.abc import Callable

import z3

from consistency.common import (
    cleanup,
)
from consistency.model.monotonic_reads import MonotonicReads
from consistency.model.monotonic_writes import MonotonicWrites
from consistency.model.read_your_writes import ReadYourWrites
from consistency.model.writes_follow_reads import WritesFollowReads


@cleanup
def test_cross_causal() -> None:
    # dynamically generate semantics
    # for each storage system
    # src provs one session semantic
    # dst needs causal
    # from bottom up
    # should look like a converging binary tree
    # overall:
    # each node should export 1 semantic
    # edge connection that node to upper layer should provide
    # all missing semantics + "glue" constraints that connects different set of symbols
    #             xc
    #            / <- mr + mw + ryw
    #         svc - wfr
    #        / <- mr + mw + wfr
    #      svc - ryw
    #     / <- mr + ryw + wfr
    #   svc - mw
    #  / <- mw + ryw + wfr
    # mr

    # take in a str (semantic short hand name)
    # return a lambda that takes a str (sub system name) and list (of symbols)
    # final list should be a list of semantic_subsystem_symbol
    def gensym(name: str) -> Callable[[str, list[str]], list[str]]:
        return lambda s, symbols: [f"{name}_{s}_{symbol}" for symbol in symbols]

    # semantic short hand name -> (assertion func, symbol gen)
    mapping = {
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
    counter = Counter(mapping.keys())

    def assertion_for(name: str, sys: str) -> z3.BoolRef:
        return mapping[name][0](mapping[name][1](sys))

    for curr, (_af, _gen) in mapping.items():
        rest = mapping.copy()
        rest.pop(curr)

        assertion_for(curr, str(counter[curr]))
        counter[curr] += 1

        # edge constraints
        assert_edges = {}
        for name, (_af2, _gen2) in rest.items():
            assert_edges[name] = assertion_for(name, str(counter[name]))
            counter[name] += 1


    # nodes = [mr, svc]
    # edges = [
    #     Edge(
    #         src=mr,
    #         dst=svc,
    #         cons=[
    #             (
    #                 Cons(
    #                     "EC",
    #                     compose(
    #                         # TODO
    #                         MonotonicWrites.assertions(),
    #                         ReadYourWrites.assertions(),
    #                         WritesFollowReads.assertions(),
    #                     ),
    #                 ),
    #             )
    #         ],
    #     )
    # ]

    # g = graph(nodes, edges)
    # ok, res = composable(g, svc)
    # assert ok

    # # mr + svc
    # mrsvc = Node(
    #     name="MRSVC",
    #     needs=[(Cons("SVC", CausalConsistency.assertions()),)],
    #     provs=[(Cons("MRSVC", extract(svc, svc, (ok, res))),)],
    # )

    # nodes = [mw, mrsvc]
    # edges = [
    #     Edge(
    #         src=mw,
    #         dst=mrsvc,
    #         cons=[
    #             (
    #                 Cons(
    #                     "EC",
    #                     compose(
    #                         MonotonicReads.assertions(),
    #                         ReadYourWrites.assertions(),
    #                         WritesFollowReads.assertions(),
    #                     ),
    #                 ),
    #             )
    #         ],
    #     )
    # ]

    # g = graph(nodes, edges)
    # ok, res = composable(g, mrsvc)
    # assert ok
