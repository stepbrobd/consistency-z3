from typing import Self

from consistency.history import History
from consistency.relation import Relation


class AbstractExecution:
    """
    Abstraction execution is built on top of a history,
    it captures the non-determinism and constraints.
    It's an event graph: ae = (H, ...rels).
    """
    hist: History
    rels: dict[str, set[Relation]]

    def __init__(
        self: Self,
        hist: History,
        **kwargs: set[Relation],
    ) -> None:
        """
        :param hist:     history.
        :param **kwargs: relations.
        """
        self.hist = hist
        self.rels = kwargs
