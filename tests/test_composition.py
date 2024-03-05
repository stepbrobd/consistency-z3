from consistency.common import compatible, compose
from consistency.model.linearizability import Linearizability
from consistency.model.monotonic_reads import MonotonicReads
from consistency.model.monotonic_writes import MonotonicWrites
from consistency.model.pram_consistency import PRAMConsistency
from consistency.model.read_your_writes import ReadYourWrites

# composition
# from the paper:
# > "As proved by Brzezinski et al. [2003], PRAM consistency is ensured iff the system provides read-your-write, monotonic reads and monotonic writes guarantee"
# meaning `compatible(pram, {ryw, mr, mw}) == True`
composed = compose(ReadYourWrites.assertions(), MonotonicReads.assertions(), MonotonicWrites.assertions())


def test_known_compatible() -> None:
    assert compatible(PRAMConsistency.assertions(), composed)
    assert compatible(Linearizability.assertions(), composed)


def test_known_incompatible() -> None:
    assert not compatible(composed, PRAMConsistency.assertions())
    assert not compatible(composed, Linearizability.assertions())
