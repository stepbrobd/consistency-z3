from abc import ABC, abstractmethod
from typing import Any

from z3 import BoolRef


class Model(ABC):
    @staticmethod
    @abstractmethod
    def assertions(symbols: list[str] | None = None, **kwargs: Any) -> BoolRef:
        pass
