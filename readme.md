# Consistency

[![Built with Nix](https://builtwithnix.org/badge.svg)](https://builtwithnix.org)

> [!Caution]
> Experimental project, use at your own risk.

Hydra Evaluation and Binary Cache:

- Jobset: <https://hydra.ysun.co/jobset/stepbrobd/consistency-z3>
- Cache: <https://cache.ysun.co/public>
- Key: `public:Y9EARSt+KLUY1JrY4X8XWmzs6uD+Zh2hRqN9eCUg55U=`

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

## What is "visible"

All below definitions have common constraint of all operations must be invoked
on the same object. The preconditions of concurrent operations include the same
object constraint anyways.

Definition of atomic operations: an operation is considered as atomic if the
logical start time equal to its logical end time.

```txt
  a1         a2
|---|      |---|

           b (rd)
       |------------|

     a3              a4
|---------|     |----------|

            a5
 |----------------------|
```

- Can view: A non-deterministic pairwise partial ordering between a write
  operation (let's call it a) and a read operation (call it b) that solely
  depends on time stamps (conceptually, the read happens after or during the
  write).
  - non-concurrent (`a1`): `op.rtime(a) < op.stime(b)` (i.e. totally ordered)
  - concurrent (`a2`):
    `And(op.stime(a) >= op.stime(b), op.stime(a) <= op.rtime(b), op.rtime(a) >= op.stime(b), op.rtime(a) <= op.rtime(b))`
  - concurrent (`a3`):
    `And(op.stime(a) <= op.stime(b), op.stime(a) <= op.rtime(b), op.rtime(a) >= op.stime(b), op.rtime(a) <= op.rtime(b))`
  - concurrent (`a4`):
    `And(op.stime(a) >= op.stime(b), op.stime(a) <= op.rtime(b), op.rtime(a) >= op.stime(b), op.rtime(a) >= op.rtime(b))`
  - concurrent (`a5`):
    `And(op.stime(a) <= op.stime(b), op.stime(a) <= op.rtime(b), op.rtime(a) >= op.stime(b), op.rtime(a) >= op.rtime(b))`

- Viewed: A non-deterministic pairwise partial ordering between a write
  operation and a read operation that builds atop "can view". Aside from the
  timestamps fall into one of the "can view" cases, `ival` of the write must
  match the `oval` of the read. In case of a write happened after or concurrent
  to the aforementioned write, viewed relation enforces the output of the read
  to be either of writes (only one can be chosen). In visible/visibility
  definition, the transitivity of viewed relation is implicitly enforced.

- Visible = viewed + arbitration: A deterministic pairwise between any
  operation.
  - Case 1: read-read pair: previous read needs to track it's closest visible
    write, then propagate the closest visible write to the latest read
  - Case 2: read-write pair: undefined for now
  - Case 3: write-read pair: simply viewed (value equivalence) + arbitration
    (preserve the previously viewed ordering as if it's a linearized ordering in
    the first place)
  - Case 4: write-write pair: undefined for now

## General guidelines

The verification/checking scopes of our tool are on the axiomatic level, i.e.
relational constraints between read/write events. When modeling a consistency
model (different from a system/protocol), users are expected to use SMT clauses
to capture the additional partial orderings of reads and writes aside from
same-object, same-session, returns-before, visibility, etc., which are
predefined as axioms in the tool as described in the non-transactional survey.
Each read/write event is represented as a product type the same way as the
non-transactional survey. Predefined axioms assign precedence to events based on
the fields of the product type. The user can define additional axioms to capture
the additional partial orderings of reads and writes, but deriving total
ordering of events in our tool possible but cumbersome. To derive total
orderings, users would need to assign a unique sortable value to `ival` and/or
`oval` of events where total ordering is needed, and extend
`AbstractExecution.arbitration` and/or `AbstractExecution.happens_before` to
reflect the total ordering by marshaling and unmarshalling the sortable values.

Relations like same-object and same-session are implemented as uninterpreted
functions taking two events as arguments. These function labels act as lookup
keys for lazily added clauses (similar to custom notations in Coq), relation
constraints are only added when first used. To create custom binary relations:

- Create a class inheriting from `consistency.relation.Relation`

- In a member function:
  - Call `op = consistency.operation.Operation.Create()` to instantiate the
    Operation sort
  - Create operation symbols using
    `a, b = consistency.operation.Operation.Consts("a b")`
  - Register the relation via `<classname>.Relation.AddConstraint`

- To use the relation:
  - Import the module
  - Call the member function with a symbolic name, e.g.:
    `rb = consistency.history.History.Relation.returns_before()`

We can compose consistency models by combining additional constraints and those
predefined axioms with logic connectives. Say we want monotonic read, in words,
a read operation can be served only by replicas that have executed all write
operations whose effects have already been observed by the requesting entity.
Axiomatically, $a, b, c \in H$, if $a \overset{vis}{\rightarrow} b$ and
$b \overset{so}{\rightarrow} c$, where $b$ and $c$ are read operations, then
$a \overset{vis}{\rightarrow} c$, i.e., the transitive closure of $vis$ and $so$
is included in $vis$.

The implementation is a literal translation of the above definition (we can also
use `z3.If` to encode the above properties, i.e. there could be multiple ways to
encode the same property, choose the one that is most readable and efficient):

```py
_, (rd, wr) = Op.Sort()
op = Op.Create()
a, b, c = Op.Consts("a b c")

so = H.Relation.session_order()
vis = AE.Relation.visibility()

# (a -vis-> b /\ b --so-> c) -> a -vis-> c
return z3.And(
    z3.ForAll(
        [a, b, c],
        z3.Implies(
            z3.And(
                op.type(b) == rd,
                op.type(c) == rd,
                vis(a, b),
                so(b, c),
            ),
            vis(a, c),
        ),
    ),
)
```

Three things you can do with consistency models, 1. standalone checking, 2.
compatibility checking between models, 3. compositions of models. The standalone
check will generate SMT clauses for the model along with all used axioms and
feed into Z3 to find whether there is at least one solution (i.e. there is at
least 1 plausible ordering of events that can satisfy all constraints of the
given model, see the test file under `tests/test_standalone.py` for the exact
usage). The compatibility check will generate SMT clauses for the negation of
the implication between two models (whether LHS implies RHS) and feed into Z3 to
find whether the negation is unsatisfiable (if usat, LHS model is guarantee to
provide all semantical constraints LHS model provides). Since the compatibility
check is not symmetric, you might need to check both directions if needed. Given
the way we define the constraints, the composition of models is a direct
conjunction of the constraints, the ordering of the composition does not affect
the result. The `compose` function takes arbitrary number of models and returns
a `z3.BoolRef`, the result can be further used in standalone checking or
compatibility checking.

When modeling a system or protocol, define an unambiguous flow graph from
consumer's perspective (the consumer here can be any entity with consistency
requirement, from a client to a server, or from a server to a server). The flow
graph should contain nodes and edges, where nodes represent entities that
require or provide consistency guarantees, and edges represent the data flow
between entities. If multiple operations are needed between two nodes, multiple
edges must be defined (the general guideline is one edge for one type, i.e. say
a client need to send request directly to a OpenAPI server, and the server
supports both GET and POST, then two edges must be defined).

A more complex example is a system with one client and one OpenAPI server, but
POST requests need to be authenticated first before being processed. In this
case, a third node needs to be defined to act as the arbitrator between the
client and the server, where clients' credentials needs to be validated on the
server side via a GET request to the arbitrator node. The flow graph should look
like this:

```txt
client ---[POST/wr]---> auth <----------------------| [GET/rd]/[reply[G]]
       <---[creds]-----                             v
       --------------------[POST(creds)/wr]-----> server
       <-------------------[reply(P)]------------
       --------------------[GET/rd]------------->
       <-------------------[reply[G]]------------
```

Although it might look like there are only 3 nodes, but in reality, each node
represents a cluster of machines that can handle the operations. To avoid
unexpected behaviors, clients' writes to auth node must be immediately be made
visible to the server, and all clients' write to the server must be causally
ordered after the POST to server requesting the credentials. To simplify the
formalization, we can enforce linearizability on auth nodes and leave server
nodes on eventual consistency if client does not care about the freshness of the
data from server. Also note that clients' states are independent of each other,
so no enforcement is needed on the client side.

```py
auth = Node(name="Auth", needs=None, provs=[(Cons("LZ", Linearizability.assertions()),)])
server = Node(name="Server", needs=None, provs=None)
client = Node(name="client", needs=None, provs=None)

nodes = [auth, server, client]
edges = [
    Edge(src=client, dst=auth, cons=None),
    Edge(src=client, dst=server, cons=None),
    Edge(src=server, dst=auth, cons=None),
]

g = graph(nodes, edges)
ok, res = composable(g, client)
assert ok
```

If more complex modelings are needed, framework users need to manually define
custom instantiations of operations and assign read/write confinement to limit
the scope of checking. Nodes and edges can be used to assign precedences of
custom operations, and application-specific constraints can be defined either on
the node edge (the checking function will add previously checked constraints to
context), and extrations of commonly used nodes and edges can be done by
individually checking the subcomponents and directly add a node with
`z3.BoolVal(True)` to treat the subcomponents as a verified node if the
subcomponent's `composable` call on a specific start node returns `True`.

Consider a streaming service with multiple components handling user
authentication, content delivery, and user interactions (simplified from
DeathStarBench Media Service). The system comprises:

- Admin: admin interface for content and user management operations
- Client: end-user interface for accessing streaming content and features
- Login: authentication service that acts like a user session manager
- User DB: user credential storage
- Metadata DB: content metadata storage
- Rent: rental transaction service
- Rent DB: transaction record storage
- Review: user review service
- Review DB: review storage
- Video: video streaming service for content delivery
- Video DB: video content storage providing

A user must first register and login through the authentication service before
accessing any content. The login service verifies credentials against the User
DB, which maintains consistent user states through Monotonic Writes and Writes
Follow Reads guarantees as updates performed by users needs to be reflected to
themselves right after.

When browsing content, the client interacts with the metadata services. Before
serving any content, users must first be authenticated through the login
service, then clients can issue read to metadata database to retrieve titles.
After selecting a media, clients can issue write to the Rent service to rent the
media for viewing. The Rent service must ensure that the title is available
through read to the metadata database. The Metadata DB provides Monotonic Reads
and Read Your Writes guarantees, allowing admin updates to be reflected visible
while tolerating some staleness for user reads.

Users can also write reviews for content they've watched. The review service
verifies content existence in Metadata DB. Writes the review to Review DB with
Read-Your-Writes ensuring users see their own reviews immediately while other
users may see slightly stale data.

Administrators use a separate interface to manage content and user access. When
uploading new content, the admin service updates metadata in Metadata DB,
uploads video content to Video DB. Both operations require prior admin
authentication (assuming admin users are pre-granted access). Video DB's Writes
Follow Reads guarantee ensures content version consistency.

The annotated flow graph can be generated by modifying the implementation in
`tests/test_media.py` and uncomment the plotting call.

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

## Meeting notes

### 2025-03-14

pre-meeting:

- lineage checked
- fixed xcy pairwise using hb instead of recursive xcy
- xcy relation (pairwise) v.s. xcy consistent (model)

```py
# how to slap a shim on any binary relation
class XCYShim(Model):
    @staticmethod
    def assertions() -> z3.BoolRef:
        _, (rd, wr) = Op.Sort()
        op = Op.Create()
        read, write = Op.Consts("read write")
        xcy = Antipode.Relation.xcy()
        return z3.And(
            op.type(read) == rd,  # type: ignore
            op.type(write) == wr,  # type: ignore
            z3.Exists(
                [write],
                z3.And(
                    op.proc(read) == op.proc(write),  # type: ignore
                    z3.ForAll([read], xcy(write, read)),
                ),
            ),
        )
```

### 2025-03-04

- just the shim layer for weak consistency + happen-before
- review lineage definition
- XCY definition currently uses hb instead of xcy (fix needed)
- low priority:
  - https://dl.acm.org/doi/10.1145/1345169.1345178
  - https://dl.acm.org/doi/10.1007/s00165-014-0303-1
  - https://link.springer.com/chapter/10.1007/978-3-319-67531-2_17
  - https://team.inria.fr/veridis/publications/

### 2025-02-20

- discharge to smt2 (working for standalone checks and compatibility checks,
  composable check not implemented)
- fix operation sort definition leaking (will only happen if using `Op.Create`
  with custom fields) in tests
- note on lamport happen-before
  (<https://microsoft.github.io/z3guide/docs/theories/Special%20Relations/#transitive-closures>):
  - transitive closure of a relation is not first-order axiomatizable
  - decision problem for ground formulas is decidable because:
    - for every binary relation over a finite domain
    - the transitive closure of the binary relation is defined over the finite
      graph of the relation

### 2025-01-31

Before meeting:

- finished happen before
- graph constraints extraction entry/exit guard
- cleanup decorator to remove side effects
- op declaration extension (maybe add op field extension to allow other types of
  op other than rd/wr?)

lineage:

- dag properties (acyclic, transitivity)
- single root: 1. all ops have a single root, 2. root have no predecessor, 3.
  paper requires lineage begins from that single root
- strict ordering within lineage: use session order, check op.proc
- service correspondence: 1. use lamport happen before, dont care about op
  type, 2. add new op field svc and check equivalence
- invocation correspondence (vague): 1. use same object 2. force wr on caller rd
  on callee
- reply correspondence: 1. use viewed, 2. inheriently undeterministic

xcy:

- tilted arrow equal to arrow? assuming equivalence
- read from lineage failing
- how to test?

After meeting:

- revisit rule 4 of lineage, how to use wr/rd
- test XCY rule 1 with only hb, and recursive definition

### 2025-01-23

Before meeting:

- `check` seem to do its job but need additional function to extract
  _equivalent_ constraints from aggregated nodes/edges
- `extract` should work properly if entry/exit node are the same
- what if entry/exit node are different? what if there are cross edges?
- when cross edges exist, should we consider all incoming edges to the aggregate
  connect to the weakest node of all nodes with outgoing edge, or the strongest
  or what else?
- antipode refactoring and tests for antipode

After meeting:

- do not allow cross edges on the aggregate nodes if there are dependencies
- if no dependency exists between the cross edge, create a new node and edge to
  simulate the constraint (functionally equivalent)

```txt
A -> B -> C
     |
     | -> D
        | ^
     E -|
```

Say BCD is an aggregate node, and for A, operations on C and D must go through
B, and operations from client E only interacts with D, users can call `extract`
on subgraph BCD with entry/exit node B and connect A through the result of the
call. And for D, user can create a completely new node say F that has an
incoming edge from E to replace D. This is functionally equivalent to the
original graph. This could only work iff. the cross edge from E to D does not
interact with rest of the subgraph BCD, and if there are dependencies, you
cannot use `extract` at all (limitation of the tool).

- antipode: use the transitive closure of vis and so for lamport happens before
- xcy should be a semantic instead of binary relation between events.

### 2025-01-17

After meeting:

- revise `check` function implementation, make sure aggregated nodes/edges
  internal behavior is consistent with external view
- add new shopping mall example to demonstrate and test the node/edge
  aggregation
- antipode XCY should be a semantic constraint, not sys/app level modeling
- data flow within a lineage can be considered as if they are within the same
  session
- revisit antipode paper sect. 4.2 (XCY is stronger than lamport causality)
- shim layer IO? experimental implementation

## License

Based on
[Consistency in Non-Transactional Distributed Storage Systems](https://arxiv.org/abs/1512.00168).

The contents inside this repository, excluding all submodules, are licensed
under the [MIT License](license.md). Third-party file(s) and/or code(s) are
subject to their original term(s) and/or license(s).
