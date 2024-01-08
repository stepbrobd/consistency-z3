import itertools

import z3
from rich import print

from consistency.common import compatible
from consistency.model.monotonic_reads import MonotonicReads
from consistency.model.monotonic_writes import MonotonicWrites
from consistency.model.pram_consistency import PRAMConsistency
from consistency.model.read_your_writes import ReadYourWrites
from consistency.model.writes_follow_reads import WritesFollowReads


def main() -> int:
    # note:
    # if a system S_1 provide guarantee G_1, another system S_2 provide guarantee G_2
    # compatible(G_1, G_2) == True means
    # the service mesh of S_1 and S_2 can be composed to provide at a guarantee of G_1
    # i.e. all assertions in G_2 are satisfied in G_1

    # compatibility is not symmetric
    # i.e. if mr is compatible with ryw, then ryw is not necessarily compatible with mr
    for a, b in itertools.product([
        # (PRAMConsistency, "pram"), # weirdly, pram seems to affect the result of other models
        (MonotonicReads, "mr"),
        (MonotonicWrites, "mw"),
        (ReadYourWrites, "ryw"),
        (WritesFollowReads, "wfr")
    ], repeat=2):
        if a == b:
            continue

        s1 = z3.Solver()
        s2 = z3.Solver()
        a[0].constraints(s1)
        b[0].constraints(s2)

        print(f"{a[1]} | {b[1]}: {compatible(s1, s2)}")

        z3.reset_params()

    # fix z3 assertion logic
    # from the paper:
    # > "As proved by Brzezinski et al. [2003], PRAM consistency is ensured iff the system provides read-your-write, monotonic reads and monotonic writes guarantee"
    # meaning `compatible(pram, {ryw, mr, mw}) == True`
    for m in [
        (MonotonicReads, "mr"),
        (MonotonicWrites, "mw"),
        (ReadYourWrites, "ryw"),
        (WritesFollowReads, "wfr"),
    ]:
        s1 = z3.Solver()
        s2 = z3.Solver()
        PRAMConsistency.constraints(s1)
        m[0].constraints(s2)

        print(f"pram | {m[1]}: {compatible(s1, s2)}")

        z3.reset_params()

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
