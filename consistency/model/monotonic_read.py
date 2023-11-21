from dataclasses import dataclass
from typing import Self

import z3


@dataclass
class MonotonicRead:
    """
    Consistency in Non-Transactional Distributed Storage Systems
    pp.{12,13}
    Section 3.4

    Monotonic reads states that successive reads must reflect a non-decreasing set of writes.

    Namely, if a process has read a certain value $v$ from an object,
    any successive read operation will not return any value written before $v$.

    Intuitively, a read operation can be served only by those replicas that have executed all
    write operations whose effects have already been observed by the requesting process.

    In effect, we can represent this by saying that, given three operations
    $a,b,c in H$ if $a -->^"vis" b$ and $b -->^"so" c$,
    where $b$ and $c$ are read operations,
    then $a -->^"vis" c$,
    i.e., the transitive closure of $vis$ and so is included in $vis$.
    """
    vis: set[str]
    so: set[str]


    def constraints(self: Self)-> list[z3.BoolRef]:
        """
        Generate the constraints for the monotonic read property.
        """
        return [z3.Implies(z3.And(a == c, b == d), z3.And((a, d) in self.vis)) for (a, b) in self.vis for (c, d) in self.so if b == c]


    def check(self: Self)-> bool:
        """
        Check if the monotonic read property holds for the given visibility and session order relations.
        """
        s = z3.Solver()
        for (a, b) in self.vis:
            for (c, d) in self.so:
                if b == c:
                    s.add(z3.Not(z3.Implies(z3.And(a == c, b == d), z3.And((a, d) in self.vis))))
        return s.check() == z3.unsat
