from abc import ABC, abstractmethod

from z3 import BoolRef


class Model(ABC):
    @staticmethod
    @abstractmethod
    def assertions() -> BoolRef:
        pass
