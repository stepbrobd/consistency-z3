from consistency.common import compatible
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
    assert compatible(PRAMConsistency.assertions(), MonotonicReads.assertions())
    assert compatible(PRAMConsistency.assertions(), MonotonicWrites.assertions())
    assert compatible(PRAMConsistency.assertions(), ReadYourWrites.assertions())


def test_known_incompatible() -> None:
    assert not compatible(MonotonicReads.assertions(), MonotonicWrites.assertions())
    assert not compatible(MonotonicReads.assertions(), PRAMConsistency.assertions())
    assert not compatible(MonotonicReads.assertions(), ReadYourWrites.assertions())
    assert not compatible(MonotonicReads.assertions(), WritesFollowReads.assertions())

    assert not compatible(MonotonicWrites.assertions(), MonotonicReads.assertions())
    assert not compatible(MonotonicWrites.assertions(), PRAMConsistency.assertions())
    assert not compatible(MonotonicWrites.assertions(), ReadYourWrites.assertions())
    assert not compatible(MonotonicWrites.assertions(), WritesFollowReads.assertions())

    assert not compatible(PRAMConsistency.assertions(), WritesFollowReads.assertions())

    assert not compatible(ReadYourWrites.assertions(), MonotonicReads.assertions())
    assert not compatible(ReadYourWrites.assertions(), MonotonicWrites.assertions())
    assert not compatible(ReadYourWrites.assertions(), PRAMConsistency.assertions())
    assert not compatible(ReadYourWrites.assertions(), WritesFollowReads.assertions())

    assert not compatible(WritesFollowReads.assertions(), MonotonicReads.assertions())
    assert not compatible(WritesFollowReads.assertions(), MonotonicWrites.assertions())
    assert not compatible(WritesFollowReads.assertions(), PRAMConsistency.assertions())
    assert not compatible(WritesFollowReads.assertions(), ReadYourWrites.assertions())
