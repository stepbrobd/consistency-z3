import itertools

import z3
from rich import print

from consistency.common import compatible
from consistency.model.monotonic_reads import MonotonicReads
from consistency.model.monotonic_writes import MonotonicWrites
from consistency.model.read_your_writes import ReadYourWrites
from consistency.model.writes_follow_reads import WritesFollowReads


def main() -> int:
    # compatibility is not symmetric
    # i.e. if mr is compatible with ryw, then ryw is not necessarily compatible with mr
    for a, b in itertools.product([
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

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
