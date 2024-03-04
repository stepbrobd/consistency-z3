# Consistency

[![Built with Nix](https://builtwithnix.org/badge.svg)](https://builtwithnix.org)

> [!Caution]
> Experimental project, use at your own risk.

Hydra Evaluation and Binary Cache:

- Jobsets: <https://hydra.nixolo.gy/jobset/stepbrobd/consistency-z3>
- Cache: <https://cache.nixolo.gy>
- Key: `cache.nixolo.gy:UDmjlw8J4sqDlBIPe5YnABPI1lkcJssN8niLozS2ltM=`

## Models

### Linearizability (arXiv:1512.00168 pp. 8)

[`consistency/model/linearizability.py`](consistency/model/linearizability.py)

Liniearizability is a conjunction between Single Order, Real Time and Return Value consistency (pp. 5). Single Order imposes a single global order that defines both visibility and arbitration (very strong, probably can't be modeled), whereas Real Time constrains arbitration to comply to the returns-before partial ordering. Finally, Return Value consistency specifies the return value consistency of a replicated data type.

### PRAM Consistency (arXiv:1512.00168 pp.11)

[`consistency/model/pram_consistency.py`](consistency/model/pram_consistency.py)

Pipeline RAM (PRAM or FIFO) consistency prescribes that all processes see write operations issued by a given process in the same order as they were invoked by that process. On the other hand, processes may observe writes issued by different processes in different orders. Thus, no global total ordering is required. However, the writes from any given process (session) must be serialized in order, as if they were in a pipeline – hence the name.

```math
PRAM \triangleq \forall a,b \in H: a\overset{so}{\rightarrow} b \Rightarrow a \overset{vis}{\rightarrow} b \triangleq so \subseteq vis
```

### Monotonic Reads (arXiv:1512.00168 pp.12)

[`consistency/model/monotonic_reads.py`](consistency/model/monotonic_reads.py)

Monotonic reads states that successive reads must reflect a non-decreasing set of writes. Namely, if a process has read a certain value v from an object, any successive read operation will not return any value written before v. Intuitively, a read operation can be served only by those replicas that have executed all write operations whose effects have already been observed by the requesting process. In effect, we can represent this by saying that, given three operations $a, b, c \in H$, if $a \overset{vis}{\rightarrow} b$ and $b \overset{so}{\rightarrow} c$, where $b$ and $c$ are read operations, then $a \overset{vis}{\rightarrow} c$, i.e., the transitive closure of $vis$ and $so$ is included in $vis$.

```math
MonotonicReads \triangleq \forall a \in H, \forall b, c \in H|_{rd}: a \overset{vis}{\rightarrow} b \wedge b \overset{so}{\rightarrow} c \Rightarrow a \overset{vis}{\rightarrow} c \triangleq (vis; so|_{rd \rightarrow rd}) \subseteq vis
```

### Read Your Writes (arXiv:1512.00168 pp.13)

[`consistency/model/read_your_writes.py`](consistency/model/read_your_writes.py)
and
[`consistency/model/read_my_writes.py`](consistency/model/read_my_writes.py)

Read-your-writes guarantee (also called read-my-writes) requires that a read operation invoked by a process can only be carried out by replicas that have already applied all writes previously invoked by the same process.

```math
ReadYourWrites \triangleq \forall a \in H|_{wr}, \forall b \in H|_{rd}: a\overset{so}{\rightarrow} b \Rightarrow a \overset{vis}{\rightarrow} b \triangleq so|_{wr \rightarrow rd} \subseteq vis
```

### Monotonic Writes (arXiv:1512.00168 pp.13)

[`consistency/model/monotonic_writes.py`](consistency/model/monotonic_writes.py)

In a system that ensures monotonic writes a write is only performed on a replica if the replica has already performed all previous writes of the same session. In other words, replicas shall apply all writes belonging to the same session according to the order in which they were issued.

```math
MonotonicWrites \triangleq \forall a, b \in H_{wr}: a\overset{so}{\rightarrow} b \Rightarrow a \overset{ar}{\rightarrow} b \triangleq so|_{wr \rightarrow wr} \subseteq ar
```

### Writes Follow Reads (arXiv:1512.00168 pp.13)

[`consistency/model/writes_follow_reads.py`](consistency/model/writes_follow_reads.py)
and
[`consistency/model/session_causality.py`](consistency/model/session_causality.py)

Writes-follow-reads, sometimes called session causality, is somewhat the converse concept of read-your-write guarantee as it ensures that writes made during the session are ordered after any writes made by any process on any object whose effects were seen by previous reads in the same session.

```math
WritesFollowReads \triangleq \forall a, c \in H|_{wr}, \forall b \in H|_{rd}: a \overset{vis}{\rightarrow} b \wedge b \overset{so}{\rightarrow} c \Rightarrow a \overset{ar}{\rightarrow} c \triangleq (vis;so|_{rd \rightarrow wr}) \subseteq ar
```

## Example

```py
from consistency.common import check, compatible
from consistency.model.linearizability import Linearizability
from consistency.model.monotonic_reads import MonotonicReads
from consistency.model.monotonic_writes import MonotonicWrites
from consistency.model.pram_consistency import PRAMConsistency
from consistency.model.read_your_writes import ReadYourWrites


# standalone
print(check(MonotonicReads.assertions())) # true

# pairwise
print(compatible(Linearizability.assertions(), PRAMConsistency.assertions())) # true

# composition
composed = compose(ReadYourWrites.assertions(), MonotonicReads.assertions(), MonotonicWrites.assertions())
print(compatible(PRAMConsistency.assertions(), composed)) # true
```

## License

Based on [Consistency in Non-Transactional Distributed Storage Systems](https://arxiv.org/abs/1512.00168).

The contents inside this repository, excluding all submodules, are licensed under the [MIT License](license.md).
Third-party file(s) and/or code(s) are subject to their original term(s) and/or license(s).
