# Consistency

[![Built with Nix](https://builtwithnix.org/badge.svg)](https://builtwithnix.org)

> [!Caution]
> Experimental project, use at your own risk.

Hydra Evaluation and Binary Cache:

- Jobsets: <https://hydra.nixolo.gy/jobset/stepbrobd/consistency-z3>
- Cache: <https://cache.nixolo.gy>
- Key: `cache.nixolo.gy:UDmjlw8J4sqDlBIPe5YnABPI1lkcJssN8niLozS2ltM=`

## Specifications

Framework user: a framework user is someone who provides node and edge
definitions (e.g. custom operations that should be supported originating from a
node, or precedences of operations) and relations to the consistency checker.

Operation: an operation is defined as a tuple of (from non-transactional
survey):

- `proc`: the process that issued the operation (used for session
  identification, e.g. same session constraint).
- `type`: the type of the operation (e.g. read, write. or custom).
- `obj`: the object the operation is performed on (e.g. a key in a key-value
  store).
- `ival`: operation input value (e.g. the value to be written, not used anywhere
  yet).
- `oval`: operation output value (e.g. the value read, not used anywhere yet).
- `stime`: invocation time of the operation (i.e. the time the operation was
  issued).
- `rtime`: response time of the operation (i.e. the time the operation was
  completed).

Think of an operation as a request-response pair, where the request is the
operation itself and the response is the operation itself with the response time
set (assuming the delays between the request and the response are equal for all
operations, the request takes `(rtime - stime)/2` time to be sent to the
handling node and to be processed, vice versa for the response).

(Our own interpretation) Operation does not contain the node that issued the
operation, nor the node that handled the operation. It's defined as a generic
entity that can be issued by any node and handled by any node. To add
constraints on the nodes that can issue or handle an operation, the framework
user must define nodes and edges.

History (in the actual writing, layout the actual Z3 clauses used to encode the
relational constraints): a set of operations. TODO: add relations between
operations within history (returns before, same session, session order).

Abstract execution (in the actual writing, layout the actual Z3 clauses used to
encode the relational constraints): one or more "instantiation" of history. An
abstract execution is a set of operations (i.e. history) that are further
constrained by the nondeterminism of the asynchronous environment (e.g., message
delivery order), and implementation-specific constraints (e.g., conflict
resolution policies) (from non-transactional survey). AE specific relations:
visibility, arbitration, happens before.

Relation predicates: a set of predicates that define the relations between
operations in a history (also includes those in AE). The predicates are used as
base/premise for consistency models (implementations in `relation.py`,
`history.py`, `abstract_execution.py`). In the implementation, the predicates
are singletons and will be added ad-hoc if any clause refers to them.

Node: node issues operations. Nodes with incoming edges can be perceived as
nodes that can handle operations issued by other nodes (servers). Nodes with
outgoing edges can be perceived as nodes that can issue operations that can be
handled by other nodes (clients). They can be used to define custom operations
(operations with types that are not read or write) that should be supported
originating from a node. Definitions of those custom operations must be provided
by the framework user and the clauses defining the custom operations must be
included in the node definition.

In the implementation, a node is defined as tuple of:

- `name`: the name, used to identify the node in a graph (can have any type, but
  must be unique).
- `needs`: a list of tuples of constraints. TODO
- `provs`: a list of tuples of constraints. TODO

Edge: edge connects nodes. Edges can be used to define the precedence of
operations on different nodes (one edge can only store exactly one type of
operation, if multiple types of operations are needed, multiple edges must be
defined). Definitions of those custom operations must be provided by the
framework user and the clauses defining the custom operations must be included
in the source node definition (specifically in the `needs` field).

Constraint: a constraint is a set of clauses that define the relations between
operations in a history (or abstract execution). Constraints can be used to
define the precedence of operations on the same node (e.g. the order of
operations issued by the same node). Or application-specific constraints (e.g.
assign data to operations' fields).

Graph: a directed multigraph that contains nodes and edges.

Compatible: compatibility is a relation between two consistency models. Two
consistency models are compatible if the the negation of the implication is
unsatisfiable (compatibility is not symmetric).

Composable: composition is an additional operator that combines two or more
consistency models into a single consistency model. It's represented as a direct
conjunction of the consistency models' constraints (the ordering of the
composition does not affect the result, relation predicates remain the same and
will only be added if any clause refers to them). Premise will be added as a
part of the composition, instead of being conjuncted with each node/edge, use
`z3.Solver.add` to add the premise to the solver. Framework users must defined
the premises as non-implicit constraints (i.e. don't use quantifiers like
`ForAll`, `Exists` and don't use `Implies`).

## Models

### Linearizability (arXiv:1512.00168 pp. 8)

[`consistency/model/linearizability.py`](consistency/model/linearizability.py)

Liniearizability is a conjunction between Single Order, Real Time and Return
Value consistency (pp. 5). Single Order imposes a single global order that
defines both visibility and arbitration (very strong, probably can't be
modeled), whereas Real Time constrains arbitration to comply to the
returns-before partial ordering. Finally, Return Value consistency specifies the
return value consistency of a replicated data type.

### PRAM Consistency (arXiv:1512.00168 pp.11)

[`consistency/model/pram_consistency.py`](consistency/model/pram_consistency.py)

Pipeline RAM (PRAM or FIFO) consistency prescribes that all processes see write
operations issued by a given process in the same order as they were invoked by
that process. On the other hand, processes may observe writes issued by
different processes in different orders. Thus, no global total ordering is
required. However, the writes from any given process (session) must be
serialized in order, as if they were in a pipeline – hence the name.

```math
PRAM \triangleq \forall a,b \in H: a\overset{so}{\rightarrow} b \Rightarrow a \overset{vis}{\rightarrow} b \triangleq so \subseteq vis
```

### Monotonic Reads (arXiv:1512.00168 pp.12)

[`consistency/model/monotonic_reads.py`](consistency/model/monotonic_reads.py)

Monotonic reads states that successive reads must reflect a non-decreasing set
of writes. Namely, if a process has read a certain value v from an object, any
successive read operation will not return any value written before v.
Intuitively, a read operation can be served only by those replicas that have
executed all write operations whose effects have already been observed by the
requesting process. In effect, we can represent this by saying that, given three
operations $a, b, c \in H$, if $a \overset{vis}{\rightarrow} b$ and
$b \overset{so}{\rightarrow} c$, where $b$ and $c$ are read operations, then
$a \overset{vis}{\rightarrow} c$, i.e., the transitive closure of $vis$ and $so$
is included in $vis$.

```math
MonotonicReads \triangleq \forall a \in H, \forall b, c \in H|_{rd}: a \overset{vis}{\rightarrow} b \wedge b \overset{so}{\rightarrow} c \Rightarrow a \overset{vis}{\rightarrow} c \triangleq (vis; so|_{rd \rightarrow rd}) \subseteq vis
```

### Read Your Writes (arXiv:1512.00168 pp.13)

[`consistency/model/read_your_writes.py`](consistency/model/read_your_writes.py)
and [`consistency/model/read_my_writes.py`](consistency/model/read_my_writes.py)

Read-your-writes guarantee (also called read-my-writes) requires that a read
operation invoked by a process can only be carried out by replicas that have
already applied all writes previously invoked by the same process.

```math
ReadYourWrites \triangleq \forall a \in H|_{wr}, \forall b \in H|_{rd}: a\overset{so}{\rightarrow} b \Rightarrow a \overset{vis}{\rightarrow} b \triangleq so|_{wr \rightarrow rd} \subseteq vis
```

### Monotonic Writes (arXiv:1512.00168 pp.13)

[`consistency/model/monotonic_writes.py`](consistency/model/monotonic_writes.py)

In a system that ensures monotonic writes a write is only performed on a replica
if the replica has already performed all previous writes of the same session. In
other words, replicas shall apply all writes belonging to the same session
according to the order in which they were issued.

```math
MonotonicWrites \triangleq \forall a, b \in H_{wr}: a\overset{so}{\rightarrow} b \Rightarrow a \overset{ar}{\rightarrow} b \triangleq so|_{wr \rightarrow wr} \subseteq ar
```

### Writes Follow Reads (arXiv:1512.00168 pp.13)

[`consistency/model/writes_follow_reads.py`](consistency/model/writes_follow_reads.py)
and
[`consistency/model/session_causality.py`](consistency/model/session_causality.py)

Writes-follow-reads, sometimes called session causality, is somewhat the
converse concept of read-your-write guarantee as it ensures that writes made
during the session are ordered after any writes made by any process on any
object whose effects were seen by previous reads in the same session.

```math
WritesFollowReads \triangleq \forall a, c \in H|_{wr}, \forall b \in H|_{rd}: a \overset{vis}{\rightarrow} b \wedge b \overset{so}{\rightarrow} c \Rightarrow a \overset{ar}{\rightarrow} c \triangleq (vis;so|_{rd \rightarrow wr}) \subseteq ar
```

## License

Based on
[Consistency in Non-Transactional Distributed Storage Systems](https://arxiv.org/abs/1512.00168).

The contents inside this repository, excluding all submodules, are licensed
under the [MIT License](license.md). Third-party file(s) and/or code(s) are
subject to their original term(s) and/or license(s).
