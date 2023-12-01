import itertools

import z3

from consistency.abstract_execution import AbstractExecution
from consistency.relation import Relation


class MonotonicRead:
    """
    Monotonic Reads are defined as:
    for all operations $a$ in history, a set of operations denoted by $H$, and,
    for all read operations $b$ and $c$ in history $H$,
    if operation $a$ is visible to operation $b$, $b$ returns before $c$ starts, and $b, c$ are in the same session,
    then operation $a$ is visible to operation $c$.
    """
    def check(ae: AbstractExecution) -> bool:
        """
        Check if the given abstract execution event graph satisfies the monotonic read properties.
        """
        solver = z3.Solver()

        # z3 vars
        vars = {op: z3.Bool(op.symbol) for op in ae.hist.ops}

        # vis, rb, ss
        for a, b in itertools.product(ae.hist.ops, repeat=2):
            print(a, b)

            # rb
            if Relation.is_rb(a, b):
                rb_rel = z3.Bool(f"rb_{a.symbol}_{b.symbol}")
                solver.add(rb_rel == z3.And(vars[a], vars[b]))

            # ss
            if Relation.is_ss(a, b):
                ss_rel = z3.Bool(f"ss_{a.symbol}_{b.symbol}")
                solver.add(ss_rel == z3.And(vars[a], vars[b]))

        # monotonic read
        for a in ae.hist['wr']:
            for b in ae.hist['rd']:
                for c in ae.hist['rd']:
                    if b != c:
                        rb_rel = z3.Bool(f"rb_{b.symbol}_{c.symbol}")
                        ss_rel = z3.Bool(f"ss_{b.symbol}_{c.symbol}")
                        so_rel = z3.And(rb_rel, ss_rel)  # $so \triangleq rb \cap ss$
                        # monotonic read condition
                        solver.add(z3.Implies(z3.And(vars[a], vars[b], so_rel), vars[c]))

        match solver.check():
            case z3.sat:
                print(solver.model())
                return True
            case z3.unsat:
                return False
            case z3.unknown:
                raise RuntimeError("MonotonicRead.check: z3 solver returned unknown")
