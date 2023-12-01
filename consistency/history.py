from typing import Self

from consistency.operation import Operation
from consistency.relation import Relation


class History:
    """
    A history is a set of operations,
    it contains all operations invoked in a given execution,
    describes the observable outcomes of executions.
    """
    ops: set[Operation]
    rel: dict[str, set[Relation]]


    def __init__(
            self: Self,
            ops: set[Operation],
            **kwargs: set[Relation]
    ) -> None:
        """
        :param ops:      set of operations.
        :param **kwargs: set of relations.
        """
        self.ops = ops
        self.rel = kwargs


    def __getitem__(self: Self, type: str) -> set[Operation]:
        """
        :param type: operation type.
        :return:     all operations of the given type.
        """
        result = set()
        for op in self.ops:
            if op.type == type:
                result.add(op)
        return result
