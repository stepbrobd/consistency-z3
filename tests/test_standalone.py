import z3

from consistency.common import check
from consistency.model.monotonic_reads import MonotonicReads
from consistency.model.monotonic_writes import MonotonicWrites
from consistency.model.pram_consistency import PRAMConsistency
from consistency.model.read_your_writes import ReadYourWrites
from consistency.model.writes_follow_reads import WritesFollowReads
from consistency.relation import Relation

# from consistency.model.linearizability import Linearizability


def test_standalone() -> None:
    models = [
        # Linearizability, # incomplete, too strong
        MonotonicReads,
        MonotonicWrites,
        PRAMConsistency,
        ReadYourWrites,
        WritesFollowReads,
    ]

    for m in models:
        assert check(m.assertions())
        Relation.Reset()
        z3.reset_params()
