from contextlib import ExitStack
from functools import partial

import z3
from rich import print


def check(s: z3.Solver, verbose=False) -> z3.ModelRef:
    solver = z3.Solver()
    for a in set(s.assertions()):
        solver.add(a)

    if verbose:
        z3.set_param("verbose", 10)
        print(f"Constraints:\n{solver.assertions()}")

        with ExitStack() as es:
            es.callback(partial(print, f"Statistics:\n{solver.statistics()}"))

    match solver.check():
        case z3.sat:
            # print(f"SAT (Model)\n{solver.model()}")
            return solver.model()
        case z3.unknown:
            # print("Unknown")
            return None
        case z3.unsat:
            # print(f"UNSAT (Counterexample)\n{solver.unsat_core()}")
            return None


def compatible(s1: z3.Solver, s2: z3.Solver, verbose=False) -> bool:
    """
    Check if all assertions in s2 are satisfiable in s1.
    True means s2 is compatible with s1.
    False means s2 is incompatible with s1.
    """
    if verbose:
        z3.set_param("verbose", 10)

    assert check(s1, verbose) is not None
    assert check(s2, verbose) is not None

    for a in set(s2.assertions()):
        s1.push()
        s1.add(a)
        if s1.check() != z3.sat:
            return False
        s1.pop()

    return True
