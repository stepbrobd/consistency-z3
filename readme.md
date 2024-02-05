# Consistency

[![Built with Nix](https://builtwithnix.org/badge.svg)](https://builtwithnix.org)

> [!Caution]
> Experimental project, use at your own risk.

Hydra Evaluation and Binary Cache:

- Jobsets: <https://hydra.nixolo.gy/jobset/stepbrobd/consistency-z3>
- Cache: <https://cache.nixolo.gy>
- Key: `cache.nixolo.gy:UDmjlw8J4sqDlBIPe5YnABPI1lkcJssN8niLozS2ltM=`

## Roadmap

- [x] basic project structure
- [x] monotonic reads
- [x] monotonic writes
- [x] read your writes
- [x] writes follow reads
- [x] z3 compatibility check
- [x] abstract pram consistency
- [ ] bounded staleness
- [ ] hand verification of pairwise compatibility

Jan. 17, 2024 - Jan. 24, 2024

- [x] bug fixes
- [x] create couple slides
- [ ] bound staleness

Jan. 24, 2024 - Jan. 31, 2024

- [x] bug fixes
- [ ] model a simple online shop

## Models

### PRAM and Sequential Consistency

#### PRAM Consistency (arXiv:1512.00168 pp.11)

[`consistency/model/pram_consistency.py`](consistency/model/pram_consistency.py)

Pipeline RAM (PRAM or FIFO) consistency prescribes that all processes see write operations issued by a given process in the same order as they were invoked by that process. On the other hand, processes may observe writes issued by different processes in different orders. Thus, no global total ordering is required. However, the writes from any given process (session) must be serialized in order, as if they were in a pipeline – hence the name.

```math
PRAM \triangleq \forall a,b \in H: a\overset{so}{\rightarrow} b \Rightarrow a \overset{vis}{\rightarrow} b \triangleq so \subseteq vis
```

Modified from original definition: $PRAM \triangleq so \subseteq vis$.

> PRAM consistency is defined as:
> for all operations $a$ and $b$ in history, a set of operations denoted by $H$,
> if operation $a$ returns before $b$ starts, and $a,b$ are in the same session,
> then operation $a$ is visible to operation $b$.

### Session Guarantees

#### Monotonic Reads (arXiv:1512.00168 pp.12)

[`consistency/model/monotonic_reads.py`](consistency/model/monotonic_reads.py)

Monotonic reads states that successive reads must reflect a non-decreasing set of writes. Namely, if a process has read a certain value v from an object, any successive read operation will not return any value written before v. Intuitively, a read operation can be served only by those replicas that have executed all write operations whose effects have already been observed by the requesting process. In effect, we can represent this by saying that, given three operations $a, b, c \in H$, if $a \overset{vis}{\rightarrow} b$ and $b \overset{so}{\rightarrow} c$, where $b$ and $c$ are read operations, then $a \overset{vis}{\rightarrow} c$, i.e., the transitive closure of $vis$ and $so$ is included in $vis$.

```math
MonotonicReads \triangleq \forall a \in H, \forall b, c \in H|_{rd}: a \overset{vis}{\rightarrow} b \wedge b \overset{so}{\rightarrow} c \Rightarrow a \overset{vis}{\rightarrow} c \triangleq (vis; so|_{rd \rightarrow rd}) \subseteq vis
```

> Monotonic Reads are defined as:
> for all operations $a$ in history, a set of operations denoted by $H$, and,
> for all read operations $b$ and $c$ in history $H$,
> if operation $a$ is visible to operation $b$, $b$ returns before $c$ starts, and $b, c$ are in the same session,
> then operation $a$ is visible to operation $c$.

#### Read Your Writes (arXiv:1512.00168 pp.13)

[`consistency/model/read_your_writes.py`](consistency/model/read_your_writes.py)
and
[`consistency/model/read_my_writes.py`](consistency/model/read_my_writes.py)

Read-your-writes guarantee (also called read-my-writes) requires that a read operation invoked by a process can only be carried out by replicas that have already applied all writes previously invoked by the same process.

```math
ReadYourWrites \triangleq \forall a \in H|_{wr}, \forall b \in H|_{rd}: a\overset{so}{\rightarrow} b \Rightarrow a \overset{vis}{\rightarrow} b \triangleq so|_{wr \rightarrow rd} \subseteq vis
```

> Read-Your-Writes are defined as:
> for all write operations $a$ in history, a set of operations denoted by $H$, and,
> for all read operations $b$ in history $H$,
> if operation $a$ returns before $b$ starts, and $a,b$ are in the same session,
> then operation $a$ is visible to operation $b$.

#### Monotonic Writes (arXiv:1512.00168 pp.13)

[`consistency/model/monotonic_writes.py`](consistency/model/monotonic_writes.py)

In a system that ensures monotonic writes a write is only performed on a replica if the replica has already performed all previous writes of the same session. In other words, replicas shall apply all writes belonging to the same session according to the order in which they were issued.

```math
MonotonicWrites \triangleq \forall a, b \in H_{wr}: a\overset{so}{\rightarrow} b \Rightarrow a \overset{ar}{\rightarrow} b \triangleq so|_{wr \rightarrow wr} \subseteq ar
```

> Monotonic Writes are defined as:
> for all write operations $a, b$ in history, a set of operations denoted by $H$,
> if operation $a$ returns before $b$ starts, and $a,b$ are in the same session,
> then operation $a$ must precede operation $b$ in the total order imposed by arbitration.

#### Writes Follow Reads (arXiv:1512.00168 pp.13)

[`consistency/model/writes_follow_reads.py`](consistency/model/writes_follow_reads.py)
and
[`consistency/model/session_causality.py`](consistency/model/session_causality.py)

Writes-follow-reads, sometimes called session causality, is somewhat the converse concept of read-your-write guarantee as it ensures that writes made during the session are ordered after any writes made by any process on any object whose effects were seen by previous reads in the same session.

```math
WritesFollowReads \triangleq \forall a, c \in H|_{wr}, \forall b \in H|_{rd}: a \overset{vis}{\rightarrow} b \wedge b \overset{so}{\rightarrow} c \Rightarrow a \overset{ar}{\rightarrow} c \triangleq (vis;so|_{rd \rightarrow wr}) \subseteq ar
```

> Writes Follow Reads are defined as:
> for all write operations $a, c$ in history, a set of operations denoted by $H$, and,
> for all read operation $b$ in history $H$,
> if operation $a$ is visible to operation $b$, and $b$ returns before $c$ starts within the same session,
> then operation $a$ must precede operation $c$ in the total order imposed by arbitration.

## Example

```py
import z3
from consistency.model.monotonic_reads import MonotonicReads
from consistency.model.monotonic_writes import MonotonicWrites
from consistency.model.pram_consistency import PRAMConsistency
from consistency.relation import Relation

def check(assertions: z3.BoolRef) -> bool:
    s = z3.Solver()
    s.add([assertions, Relation.Constraints()])
    return s.check() == z3.sat

def compatible(lhs: z3.BoolRef, rhs: z3.BoolRef) -> bool:
    s = z3.Solver()
    s.add([z3.Not(z3.Implies(lhs, rhs)), Relation.Constraints()])
    return s.check() == z3.unsat

def compose(*assertions: z3.BoolRef) -> z3.BoolRef:
    return z3.And(*assertions)

# standalone
s1 = z3.Solver()
print(check(MonotonicReads.assertions()))

# pairwise: lhs <- rhs
s2 = z3.Solver()
print(compatible(MonotonicReads.assertions(), MonotonicWrites.assertions()))

# composition
s3 = z3.Solver()
print(compatible(compose(MonotonicReads.assertions(), MonotonicWrites.assertions()), PRAMConsistency.assertions()))
```

## License

Based on [Consistency in Non-Transactional Distributed Storage Systems](https://arxiv.org/abs/1512.00168).

The contents inside this repository, excluding all submodules, are licensed under the [MIT License](license.md).
Third-party file(s) and/or code(s) are subject to their original term(s) and/or license(s).
