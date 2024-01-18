import itertools

import z3
from rich import print

from consistency.model.monotonic_reads import MonotonicReads
from consistency.model.monotonic_writes import MonotonicWrites
from consistency.model.pram_consistency import PRAMConsistency
from consistency.model.read_your_writes import ReadYourWrites
from consistency.model.writes_follow_reads import WritesFollowReads
from consistency.relation import Relation


def check(assertions: z3.BoolRef) -> bool:
    s = z3.Solver()
    s.add([assertions, Relation.Constraints()])
    return s.check() == z3.sat


def compatible(lhs: z3.BoolRef, rhs: z3.BoolRef) -> bool:
    s = z3.Solver()
    s.add([z3.Not(z3.Implies(lhs, rhs)), Relation.Constraints()])
    return s.check() == z3.unsat


def compose(*assertions: z3.BoolRef) -> z3.BoolRef:
    return z3.And(*assertions)


# this week:
# fix bugs
# couple slides
# bounded staleness
def main() -> int:
    models = [
        MonotonicReads,
        MonotonicWrites,
        PRAMConsistency,
        ReadYourWrites,
        WritesFollowReads,
    ]

    # standalone
    print("Standalone:")
    for m in models:
        print(f"{m.__name__}: {check(m.assertions())}")
        Relation.Reset()
        z3.reset_params()

    # pairwise
    # note:
    # if a system S_1 provide guarantee G_1, another system S_2 provide guarantee G_2
    # compatible(G_1, G_2) == True means
    # the service mesh of S_1 and S_2 can be composed to provide at a guarantee of G_1
    # i.e. all assertions in G_2 are satisfied in G_1
    # note:
    # compatibility is not symmetric
    # i.e. if mr is compatible with ryw, then ryw is not necessarily compatible with mr
    print("Pairwise:")
    for lhs, rhs in itertools.product(models, repeat=2):
        if lhs == rhs:
            continue

        print(f"{lhs.__name__} <- {rhs.__name__}: {compatible(lhs.assertions(), rhs.assertions())}")
        Relation.Reset()
        z3.reset_params()

    # composition
    # from the paper:
    # > "As proved by Brzezinski et al. [2003], PRAM consistency is ensured iff the system provides read-your-write, monotonic reads and monotonic writes guarantee"
    # meaning `compatible(pram, {ryw, mr, mw}) == True`
    print("Composition:")
    composed = compose(ReadYourWrites.assertions(), MonotonicReads.assertions(), MonotonicWrites.assertions())
    print(f"PRAM <- {{RYW, MR, MW}}: {compatible(PRAMConsistency.assertions(), composed)}")
    print(f"{{RYW, MR, MW}} <- PRAM: {compatible(composed, PRAMConsistency.assertions())}")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
