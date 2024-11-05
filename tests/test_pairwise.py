from consistency.common import compatible
from consistency.model.causal_consistency import CausalConsistency
from consistency.model.linearizability import Linearizability
from consistency.model.monotonic_reads import MonotonicReads
from consistency.model.monotonic_writes import MonotonicWrites
from consistency.model.pram_consistency import PRAMConsistency
from consistency.model.read_your_writes import ReadYourWrites
from consistency.model.writes_follow_reads import WritesFollowReads

# if a system S_1 provide guarantee G_1, another system S_2 provide guarantee G_2
# compatible(G_1, G_2) == True means
# the service mesh of S_1 and S_2 can be composed to provide at a guarantee of G_1
# i.e. all assertions in G_2 are satisfied in G_1
# note:
# compatibility is not symmetric
# i.e. if mr is compatible with ryw, then ryw is not necessarily compatible with mr


def test_known_compatible() -> None:
    assert compatible(CausalConsistency.assertions(), MonotonicReads.assertions())
    assert compatible(CausalConsistency.assertions(), MonotonicWrites.assertions())
    assert compatible(CausalConsistency.assertions(), PRAMConsistency.assertions())
    assert compatible(CausalConsistency.assertions(), ReadYourWrites.assertions())
    # FIXME: failing causal <- wfr
    assert compatible(CausalConsistency.assertions(), WritesFollowReads.assertions())

    assert compatible(Linearizability.assertions(), MonotonicReads.assertions())
    assert compatible(Linearizability.assertions(), MonotonicWrites.assertions())
    assert compatible(Linearizability.assertions(), PRAMConsistency.assertions())
    assert compatible(Linearizability.assertions(), ReadYourWrites.assertions())
    assert compatible(Linearizability.assertions(), WritesFollowReads.assertions())

    assert compatible(PRAMConsistency.assertions(), MonotonicReads.assertions())
    assert compatible(PRAMConsistency.assertions(), MonotonicWrites.assertions())
    assert compatible(PRAMConsistency.assertions(), ReadYourWrites.assertions())


def test_known_incompatible() -> None:
    assert not compatible(CausalConsistency.assertions(), Linearizability.assertions())

    assert not compatible(MonotonicReads.assertions(), Linearizability.assertions())
    assert not compatible(MonotonicReads.assertions(), MonotonicWrites.assertions())
    assert not compatible(MonotonicReads.assertions(), PRAMConsistency.assertions())
    assert not compatible(MonotonicReads.assertions(), ReadYourWrites.assertions())
    assert not compatible(MonotonicReads.assertions(), WritesFollowReads.assertions())

    assert not compatible(MonotonicWrites.assertions(), CausalConsistency.assertions())
    assert not compatible(MonotonicWrites.assertions(), Linearizability.assertions())
    assert not compatible(MonotonicWrites.assertions(), MonotonicReads.assertions())
    assert not compatible(MonotonicWrites.assertions(), PRAMConsistency.assertions())
    assert not compatible(MonotonicWrites.assertions(), ReadYourWrites.assertions())
    assert not compatible(MonotonicWrites.assertions(), WritesFollowReads.assertions())

    assert not compatible(PRAMConsistency.assertions(), CausalConsistency.assertions())
    assert not compatible(PRAMConsistency.assertions(), Linearizability.assertions())
    assert not compatible(PRAMConsistency.assertions(), WritesFollowReads.assertions())

    assert not compatible(ReadYourWrites.assertions(), CausalConsistency.assertions())
    assert not compatible(ReadYourWrites.assertions(), Linearizability.assertions())
    assert not compatible(ReadYourWrites.assertions(), MonotonicReads.assertions())
    assert not compatible(ReadYourWrites.assertions(), MonotonicWrites.assertions())
    assert not compatible(ReadYourWrites.assertions(), PRAMConsistency.assertions())
    assert not compatible(ReadYourWrites.assertions(), WritesFollowReads.assertions())

    assert not compatible(WritesFollowReads.assertions(), CausalConsistency.assertions())
    assert not compatible(WritesFollowReads.assertions(), Linearizability.assertions())
    assert not compatible(WritesFollowReads.assertions(), MonotonicReads.assertions())
    assert not compatible(WritesFollowReads.assertions(), MonotonicWrites.assertions())
    assert not compatible(WritesFollowReads.assertions(), PRAMConsistency.assertions())
    assert not compatible(WritesFollowReads.assertions(), ReadYourWrites.assertions())
