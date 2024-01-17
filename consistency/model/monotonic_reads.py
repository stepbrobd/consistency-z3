import itertools

import z3

from consistency.abstract_execution import AbstractExecution
from consistency.constraint import Constraint
from consistency.relation import Relation


class MonotonicReads:
    """
    Monotonic Reads are defined as:
    for all operations $a$ in history, a set of operations denoted by $H$, and,
    for all read operations $b$ and $c$ in history $H$,
    if operation $a$ is visible to operation $b$, $b$ returns before $c$ starts, and $b, c$ are in the same session,
    then operation $a$ is visible to operation $c$.
    """
    @staticmethod
    def constraints(s: z3.Solver) -> None:
        """
        Add monotonic read constraints.
        """
        _, (rd, wr) = Constraint.declare_operation_type()
        op = Constraint.declare_operation()
        a, b, c = Constraint.declare_operation_symbols("a b c")

        so = Constraint.session_order(s)
        vis = Constraint.visibility(s)

        # monotonic read
        s.add(z3.ForAll([a, b, c],
                z3.Implies(
                    z3.And(vis(a, b), so(b, c), op.type(b) == rd, op.type(c) == rd),
                    vis(a, c)
                )
        ))


    @staticmethod
    def check(ae: AbstractExecution) -> bool:
        """
        Check if the given abstract execution event graph satisfies the monotonic read properties.
        """
        z3.set_param(proof=True)
        solver = z3.Solver()

        # z3 vars
        vars = {op: z3.Bool(op.symbol) for op in ae.hist.ops}

        # vis, rb, ss
        for a, b in itertools.product(ae.hist.ops, repeat=2):
            # visibility
            if Relation(sub=a, obj=b) in ae.rels["vis"]:
                print(f"{a.symbol} --vis-> {b.symbol}")
                vis_rel = z3.Bool(f"{a.symbol}_vis_{b.symbol}")
                solver.add(vis_rel == z3.And(vars[a], vars[b]))

            # session-order = read-before + same-session
            # if Relation.is_so(a, b):
            #     print(f"{a.symbol} --so-> {b.symbol}")
            #     so_rel = z3.Bool(f"{a.symbol}_so_{b.symbol}")
            #     solver.add(so_rel == (vars[a] and vars[b]))

            # returns-before
            if Relation.is_rb(a, b):
                print(f"{a.symbol} --rb-> {b.symbol}")
                rb_rel = z3.Bool(f"{a.symbol}_rb_{b.symbol}")
                solver.add(rb_rel == z3.And(vars[a], vars[b]))

            # same-session
            if Relation.is_ss(a, b):
                print(f"{a.symbol} --ss-> {b.symbol}")
                ss_rel = z3.Bool(f"{a.symbol}_ss_{b.symbol}")
                solver.add(ss_rel == z3.And(vars[a], vars[b]))

        # monotonic read
        for a in ae.hist["wr"]:
            for b in ae.hist["rd"]:
                for c in ae.hist["rd"]:
                    if b != c:
                        vis_ab = z3.Bool(f"{a.symbol}_vis_{b.symbol}")
                        vis_ac = z3.Bool(f"{a.symbol}_vis_{c.symbol}")
                        rb_bc = z3.Bool(f"{b.symbol}_rb_{c.symbol}")
                        ss_bc = z3.Bool(f"{b.symbol}_ss_{c.symbol}")
                        so_bc = z3.And(rb_bc, ss_bc)
                        solver.add(z3.Implies(z3.And(vis_ab, so_bc), vis_ac))

        match solver.check():
            case z3.sat:
                # print(solver.proof())
                print(solver.model())
                return True
            case z3.unsat:
                return False
            case z3.unknown:
                raise RuntimeError("MonotonicRead.check: z3 solver returned unknown")
