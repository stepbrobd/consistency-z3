import z3

from consistency.abstract_execution import AbstractExecution
from consistency.constraint import Constraint


class MonotonicWrites:
    @staticmethod
    def constraints(s: z3.Solver) -> None:
        _, (rd, wr) = Constraint.declare_operation_type()
        op = Constraint.declare_operation()
        ...


    @staticmethod
    def check(ae: AbstractExecution) -> bool:
        ...
