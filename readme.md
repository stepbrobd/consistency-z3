# Consistency

[![Built with Nix](https://builtwithnix.org/badge.svg)](https://builtwithnix.org)

> [!Caution]
> Experimental project, use at your own risk.

## Model

### Session Guarantees

#### Monotonic Reads (arXiv:1512.00168 pp.12)

Monotonic reads states that successive reads must reflect a non-decreasing set of writes. Namely, if a process has read a certain value v from an object, any successive read operation will not return any value written before v. Intuitively, a read operation can be served only by those replicas that have executed all write operations whose effects have already been observed by the requesting process. In effect, we can represent this by saying that, given three operations $a, b, c \in H$, if $a \overset{vis}{\rightarrow} b$ and $b \overset{so}{\rightarrow} c$, where $b$ and $c$ are read operations, then $a \overset{vis}{\rightarrow} c$, i.e., the transitive closure of $vis$ and $so$ is included in $vis$.
$$
MonotonicReads \triangleq \forall a \in H, \forall b, c \in H|_{rd}: a \overset{vis}{\rightarrow} b \wedge b \overset{so}{\rightarrow} c \Rightarrow a \overset{vis}{\rightarrow} c \triangleq (vis; so|_{rd \rightarrow rd}) \subseteq vis
$$
> Monotonic Reads are defined as:
> for all operations $a$ in history, a set of operations denoted by $H$, and,
> for all read operations $b$ and $c$ in history $H$,
> if operation $a$ is visible to operation $b$, $b$ returns before $c$ starts, and $b, c$ are in the same session,
> then operation $a$ is visible to operation $c$.

#### Read Your Writes (arXiv:1512.00168 pp.13)

Read-your-writes guarantee (also called read-my-writes) requires that a read operation invoked by a process can only be carried out by replicas that have already applied all writes previously invoked by the same process.
$$
ReadYourWrites \triangleq \forall a \in H|_{wr}, \forall b \in H|_{rd}: a\overset{so}{\rightarrow} b \Rightarrow a \overset{vis}{\rightarrow} b \triangleq so|_{wr \rightarrow rd} \subseteq vis
$$
> Read-Your-Writes are defined as:
> for all write operations $a$ in history, a set of operations denoted by $H$, and,
> for all read operations $b$ in history $H$,
> if operation $a$ returns before $b$ starts, and $a,b$ are in the same session,
> then operation $a$ is visible to operation $b$.

## Abstract Definition

- Check the formal definition of a consistency model (WIP)
- Check the pairwise compatibility of consistency models (WIP)
- ...

Example:

```py
import z3
from consistency.common import check
from consistency.model.monotonic_read import MonotonicRead
from consistency.model.read_your_writes import ReadYourWrites

s = z3.Solver()
MonotonicRead.constraints(s)
ReadYourWrites.constraints(s)
check(s)
```

## Concrete History

- Check the consistency of a concrete history (WIP)
- ...

Example:

```py
# log parser is not implemented yet
op_a = Operation(
    symbol="a",
    proc=1,
    type="wr",
    obj=1,
    ival=("somekey", "someval"),
    oval=None,
    stime=0,
    rtime=1,
)
op_b = Operation(
    symbol="b",
    proc=2,
    type="rd",
    obj=1,
    ival="somekey",
    oval="someval",
    stime=2,
    rtime=3,
)
op_c = Operation(
    symbol="c",
    proc=2,
    type="rd",
    obj=1,
    ival="somekey",
    oval="someval",
    stime=4,
    rtime=5,
)
# a --vis-> b
vis = {Relation(sub=op_a, obj=op_b)}
# b --so-> c
rb = {Relation(sub=op_b, obj=op_c)}
ss = {Relation(sub=op_b, obj=op_c)}
hist = History(
    ops={op_a, op_b, op_c},
    rb=rb,
    ss=ss,
)
ae = AbstractExecution(
    hist=hist,
    vis=vis,
)
print(MonotonicRead.check(ae))
```

## License

Based on [Consistency in Non-Transactional Distributed Storage Systems](https://arxiv.org/abs/1512.00168).

The contents inside this repository, excluding all submodules, are licensed under the [MIT License](license.md).
Third-party file(s) and/or code(s) are subject to their original term(s) and/or license(s).
