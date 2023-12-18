import z3

from consistency.abstract_execution import AbstractExecution


class ReadYourWrites:
    """
    Read-Your-Writes are defined as:
    for all write operations $a$ in history, a set of operations denoted by $H$, and,
    for all read operations $b$ in history $H$,
    if operation $a$ returns before $b$ starts, and $a,b$ are in the same session,
    then operation $a$ is visible to operation $b$.
    """
    @staticmethod
    def constraints(s: z3.Solver, op: z3.DatatypeSortRef) -> None:
        """
        Add read-your-writes constraints.
        """
        # ops a, b
        a = z3.Const("a", op)
        b = z3.Const("b", op)

        # returns-before
        rb = z3.Function("rb", op, op, z3.BoolSort())
        s.add(z3.ForAll(
            [a, b],
            z3.Implies(rb(a, b), op.rtime(a) < op.stime(b))
        ))

        # same-session
        ss = z3.Function("ss", op, op, z3.BoolSort())
        s.add(z3.ForAll(
            [a, b],
            z3.Implies(ss(a, b), op.proc(a) == op.proc(b))
        ))

        # session-order
        so = z3.Function("so", op, op, z3.BoolSort())
        s.add(z3.ForAll(
            [a, b],
            z3.Implies(so(a, b), z3.And(rb(a, b), ss(a, b)))
        ))

        # visibility
        vis = z3.Function("vis", op, op, z3.BoolSort())
        s.add(z3.ForAll(
            [a, b],
            z3.Implies(
                vis(a, b),
                z3.And(op.type(a) == "wr", op.type(b) == "rd", op.obj(a) == op.obj(b), op.rtime(a) < op.stime(b))
            )
        ))

        # read-your-writes
        s.add(z3.ForAll(
            [a, b],
            z3.Implies(
                z3.And(so(a, b), op.type(a) == "wr", op.type(b) == "rd"),
                vis(a, b)
            )
        ))


    @staticmethod
    def check(ae: AbstractExecution) -> bool:
        ...
