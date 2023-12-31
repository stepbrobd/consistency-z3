
import z3

from consistency.common import compatible
from consistency.model.monotonic_reads import MonotonicReads
from consistency.model.read_your_writes import ReadYourWrites


def main() -> int:
    mr = z3.Solver()
    MonotonicReads.constraints(mr)

    ryw = z3.Solver()
    ReadYourWrites.constraints(ryw)

    # compatibility is not symmetric
    # i.e. if mr is compatible with ryw, then ryw is not necessarily compatible with mr
    print(compatible(mr, ryw))
    print(compatible(ryw, mr))

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
