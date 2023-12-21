import z3
from rich import print


def check(s: z3.Solver) -> bool:
    print(f"Constraints:\n{s.assertions()}")
    match s.check():
        case z3.sat:
            print(f"SAT (Model)\n{s.model()}")
            return True
        case z3.unknown:
            print("Unknown")
            return False
        case z3.unsat:
            print(f"UNSAT (Counterexample)\n{s.unsat_core()}")
            return False
