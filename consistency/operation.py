from typing import Any, NamedTuple


class Operation(NamedTuple):
    """
    An operation is a tuple of (proc, type, obj, ival, oval, stime, rtime).
    """
    proc: int # process id
    type: str # operation type
    obj: int # object id
    ival: Any # input value
    stime: int # start time
    rtime: int = None # return time
    oval: Any = None # output value
    symbol: str = None # readable representation
