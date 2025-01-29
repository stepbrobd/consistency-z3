from consistency.common import cleanup, compatible, compose
from consistency.model.linearizability import Linearizability
from consistency.model.monotonic_reads import MonotonicReads
from consistency.model.monotonic_writes import MonotonicWrites
from consistency.model.read_your_writes import ReadYourWrites
from consistency.model.writes_follow_reads import WritesFollowReads

# composition
# from the paper:
# > "As proved by Brzezinski et al. [2003], PRAM consistency is ensured iff the system provides read-your-write, monotonic reads and monotonic writes guarantee"
# meaning `compatible(pram, {ryw, mr, mw}) == True`
pram_alt = compose(ReadYourWrites.assertions(), MonotonicReads.assertions(), MonotonicWrites.assertions())
causal_alt = compose(ReadYourWrites.assertions(), MonotonicReads.assertions(), MonotonicWrites.assertions(), WritesFollowReads.assertions())


@cleanup
def test_known_compatible() -> None:
    assert compatible(Linearizability.assertions(), causal_alt)
    assert compatible(Linearizability.assertions(), pram_alt)
    assert compatible(causal_alt, pram_alt)


@cleanup
def test_known_incompatible() -> None:
    assert not compatible(causal_alt, Linearizability.assertions())
    assert not compatible(pram_alt, Linearizability.assertions())
    assert not compatible(pram_alt, causal_alt)
