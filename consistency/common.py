from contextlib import ExitStack
from functools import partial

import z3
from rich import print


def check(s: z3.Solver) -> bool:
    solver = z3.Solver()
    for a in set(s.assertions()):
        solver.add(a)

    print(f"Constraints:\n{solver.assertions()}")

    with ExitStack() as es:
        es.callback(partial(print, f"Statistics:\n{solver.statistics()}"))

    match solver.check():
        case z3.sat:
            print(f"SAT (Model)\n{solver.model()}")
            return True
        case z3.unknown:
            print("Unknown")
            return False
        case z3.unsat:
            print(f"UNSAT (Counterexample)\n{solver.unsat_core()}")
            return False
