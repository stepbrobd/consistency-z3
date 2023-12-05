from typing import NamedTuple

from consistency.operation import Operation


class Relation(NamedTuple):
    """
    A relation between two operations.
    """
    sub: Operation
    obj: Operation


    @staticmethod
    def is_rb(a: Operation, b: Operation) -> bool:
        """
        Return True if the given operations are related by the read-before relation,
        that is,  $rb \triangleq \\{(a, b): a, b \\in H \\wedge a.rtime < b.stime\\}$.
        """
        return a.rtime is not None and b.stime is not None and a.rtime < b.stime


    @staticmethod
    def is_ss(a: Operation, b: Operation) -> bool:
        """
        Return True if the given operations are related by the same-session relation,
        that is, $ss \triangleq \\{(a, b): a, b \\in H \\wedge a.proc = b.proc\\}$.
        """
        return a.proc is not None and b.proc is not None and a.proc == b.proc


    @staticmethod
    def is_so(a: Operation, b: Operation) -> bool:
        """
        Return True if the given operations are related by the same-order relation,
        that is, $so \triangleq rb \\cap ss$.
        """
        return Relation.is_rb(a, b) and Relation.is_ss(a, b)


    @staticmethod
    def is_ob(a: Operation, b: Operation) -> bool:
        """
        Return True if the given operations are related by the same-object relation,
        that is, $ob \triangleq \\{(a, b): a, b \\in H \\wedge a.obj = b.obj\\}$.
        """
        return a.obj is not None and b.obj is not None and a.obj == b.obj


    @staticmethod
    def is_concur(a: Operation, b: Operation) -> bool:
        """
        Return True if the given operations are related by the concurrent relation,
        that is, $concur \triangleq ob \backslash rb$.
        """
        return Relation.is_ob(a, b) and not Relation.is_rb(a, b)
