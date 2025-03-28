= Introduction

Modern distributed systems often relax strict consistency guarantees to achieve
scalability, fault tolerance, and low latency operations. Understanding and
comparing different forms of relaxed consistency semantics is crucial for both
system designers and researchers. Yet, systematically modeling and reasoning
about these semantics, as well as their compositional properties, remained a
understudied area.

Our framework aims to bridge this gap by providing a SMT-based approach to
encode and analyze the safety properties of weaker consistency models (comparing
with linearizability), and their compositions under the assumption of livenss
properties are always satisfied, i.e. eventual consistency is guaranteed, and we
are layering everything on top of it. By offering semi-formal, logical
representation of operations, our system can generate proof witnesses about the
satisfiability of specific consistency properties, or the compatibility and
composability between multiple models. This approach enables fast exploration
and iteration of alternative system designs, guiding the development adhere to
intended consistency guarantees from the very beginning.

// TODO: rewrite after wrapping up

= Consistency Semantics

In Viotti et al. @viotti2016consistency, authors provided a structured overview
of different consistency semantics appeared in distributed systems. Building
upon it's semantic definitions, we propose to use predicate logic derived from
those definitions to model consistency semantics, and reason about the
compositional properties of these semantics with SMT solvers (while Z3
@demoura2008z3 is used in our implementation, it's easily extensible with other
solver backends like CVC5 @barbosa2022cvc5).

// TODO: summarize operations, axioms, and models

However, our current framework abstracts system-wide behavior from a single
node's perspective, applying constraints to operations primarily within the
scope of a single history and its corresponding abstract executions. While this
focuses the analysis and simplifies reasoning on local consistency properties
from the observing node's perspective, it also means that global behaviors
across multiple nodes may need additional modeling.

== Operations

To capture complex behaviors in distributed system executions, we model state
transitions on individual nodes using the notion of *operations*. Similar to
Viotti et al. @viotti2016consistency, we define an operation as a tuple
containing: `proc` (process or node), `type` (read or write), `obj` (the object
being acted upon), `ival` (input value), `oval` (output value), `stime`
(start time), and `rtime` (return time). In our SMT encoding, this tuple is
modeled as a sort, serving as the atomic building block for capturing system
behaviors and state transition constraints.

Partial and total orderings of operations are assigned through relation
functions defined in history and abstract execution @burckhardt2014principles
@viotti2016consistency. In the implementation, they are defined as uninterpreted
functions with constraints @bryant2002modeling. History represent the set of all
operations executed in the system, while abstract execution instantiates/refines
the history by specifying which operations are visible to, or are arbitrated
over each other. By embedding these relations in first order logic, we can
leverage SMT solvers to check the satisfiability of a given configuration,
thereby determining whether a particular consistency model holds or if certain
axioms of that model are violated.

/* FIXME: from readme
*
* these are more relevant to composition, add them here won't make much sense?
*
* Operation: an operation is defined as a tuple of (from non-transactional survey):
* proc: the process that issued the operation (used for session identification, e.g. same session constraint).
* type: the type of the operation (e.g. read, write. or custom).
* obj: the object the operation is performed on (e.g. a key in a key-value store).
* ival: operation input value (e.g. the value to be written, not used anywhere yet).
* oval: operation output value (e.g. the value read, not used anywhere yet).
* stime: invocation time of the operation (i.e. the time the operation was issued).
* rtime: response time of the operation (i.e. the time the operation was completed).
* Think of an operation as a request-response pair, where the request is the operation itself and the response is the operation itself with the response time set (assuming the delays between the request and the response are equal for all operations, the request takes (rtime - stime)/2 time to be sent to the handling node and to be processed, vice versa for the response).
*
* (Our own interpretation)
* Operation does not contain the node that issued the operation, nor the node that handled the operation. It's defined as a generic entity that can be issued by any node and handled by any node. To add constraints on the nodes that can issue or handle an operation, the framework user must define nodes and edges.
*/

== Axiom

/*
* Relation predicates:
* A set of predicates that define the relations between operations in a history (also includes those in AE).
* The predicates are used as base/premise for consistency models (implementations in relation.py, history.py, abstract_execution.py). In the implementation, the predicates are singletons and will be added ad-hoc if any clause refers to them.
*/
Similar to how Lamport et al. @lamport1977proving defines axioms, they are
operational invariants defined over operations. In our implementation, these
axioms/invariants/relations are declared as uninterpreted functions, where the
SMT solvers are free to interpret them so long as they satisfy the imposed
constraints.

=== History

/*
* History (in the actual writing, layout the actual Z3 clauses used to encode the relational constraints): a set of operations.
* Add relations between operations within history (returns before, same session, session order).
*/

A history is a set of operations that have been executed in the system the tool
is modeling @viotti2016consistency. Although it is not specifically defined as
such in our framework, relations are quantified over operations to capture the
*deterministic* orderings of themselves and other operations in the history. The
operations being quantified over, forms the history of, which is conceptually
identical to the set of operations that have been executed in the system.

Axioms defined for operations within a history:

- returns-before: $"rb" eq.delta {(a, b) : a, b in H and a."rtime" < b."stime"}$

- same-session: $"ss" eq.delta {(a, b) : a, b in H and a."proc" = b."proc"}$

- session-order: $"so" eq.delta "rb" sect "ss"$

- same-object: $"ob" eq.delta {(a, b) : a, b in H and a."obj" = b."obj"}$

=== Abstract Execution

/*
* Abstract execution (in the actual writing, layout the actual Z3 clauses used to
* encode the relational constraints): one or more "instantiation" of history. An
* abstract execution is a set of operations (i.e. history) that are further
* constrained by the nondeterminism of the asynchronous environment (e.g., message
* delivery order), and implementation-specific constraints (e.g., conflict
* resolution policies) (from non-transactional survey).
*/

Abstract executions are instantiated from a given history by specifying which
operations are visible to each other and how they are ordered. Multiple multiple
abstract executions are possible for a single history as observed event oderings
can differ between nodes. AE encode the *non-deterministic* effects of
asynchronous execution environments and implementation-specific constraints
@burckhardt2014principles @viotti2016consistency.

Axioms defined for operations within abstract executions:

- visibility (vis): visibility definition used in all literatures we've reviewed
  are ambiguous
in the sense that they don't specify the exact behavior under concurrent
settings @viotti2016consistency @viotti2016towards @zhang2018building
@ferreira2023antipode. In our implementation, we restructured visibility as a
binary relation and performed explicit case analysis on all possible
combinations of read and write operations that can be "visible" to each other.
To achieve visibility, two operations must first fall in one of the categories
in "can-view":

// FIXME: way too ugly
can-view (cv): $"cv" eq.delta {(a, b) : a in H_"rd", b in H_"wr" and a."obj" = b."obj" and (
a."stime" > b."rtime" // non-concurrent
or
(a."stime" <= b."stime" and a."stime" <= b."rtime" and a."rtime" >= b."stime" and a."rtime" >= b."rtime")
or
(a."stime" >= b."stime" and a."stime" <= b."rtime" and a."rtime" >= b."stime" and a."rtime" >= b."rtime")
or
(a."stime" <= b."stime" and a."stime" <= b."rtime" and a."rtime" >= b."stime" and a."rtime" <= b."rtime")
or
(a."stime" >= b."stime" and a."stime" <= b."rtime" and a."rtime" >= b."stime" and a."rtime" <= b."rtime")
)}$

In the above encoding, "can-view" is defined as a non-deterministic pairwise
partial ordering that solely depends on time stamps (conceptually, it captures
all cases where reads happened before or after or during writes). And is a set
of operations where, the first element of the tuple is a read and the second
element is a write. The read *can view* (nondeterminism included) the write if:

+ (a1) The read-write pair contains non-concurrent operations.

+ (a2) The read started before the write starts and ended after the write ends.

+ (a3) The read started after the write starts and ended after the write ends.

+ (a4) The read started before the write starts and ended before the write ends.

+ (a5) The read started after the write starts and ended before the write ends.

#align(center)[
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
]

While "can-view" captures the possible visibility between read and write, the
result dependency between them is captured by the "viewed" relation:

$"viewed" eq.delta {(a, b) : a in H_"rd", b in H_"wr" and (
a."oval" = b."ival"
or
(exists x in H_"wr" and (x, b) in "cv" and a."oval" = x."ival")
)}$

In the encoding above, "viewed" is a non-deterministic pairwise partial ordering
between a write and a read that build atop "can-view". Aside from the timestamps
fall into one of the "can-view" cases, we assigned additional value related
constraints to operations: either the input of the write must match the output
of the read, or, in case of a write happened after or concurrent to the
aforementioned write, viewed relation enforces the output of the read to be
either of writes (but only one can be chosen). In visibility definition, the
transitivity of viewed relation is implicitly enforced.

// actual vis
In our visible/visibility definition, it is defined as a *deterministic* binary
relationship between any two operations in the history. It also enforces the
transitivity (propagation) and acyclicity (cannot go back in time) of the viewed
relation. We do not enforce transitivity and acyclicity in the viewed relation
as the orderings of concurrent operations are non-deterministic, and viewed
should include all pairs of operations that can be viewed by each other only
from logical time and value equality perspective. The following cases are
considered:

// simplest form: can-view -> viewed -> vis + ar
+ write-read: $"viewed" sect "ar"$, simply viewed (value equivalence) +
  arbitration (preserve the previously viewed ordering as if it's a linearized
  ordering in the first place)

+ write-write: no constraints

// later read tracks earlier read's closest visible write
// FIXME: probably wrong
+ read-read: ${(a, b) : a, b in H_"rd" and (exists x in H_"wr" and (x, a) in "vis") arrow (x, b)}$,
  previous read needs to track it's closest visible write, then propagate the
  closest visible write to the latest read

+ read-write: no constraints

// FIXME: rework needed
Note that the read-read case is recursively defined, where $a$ and $b$ are in $"vis"_"read-read"$ iff.
there's a write $x$ that is visible to $a$ and $x$ is in $"vis"_"read-read"$ with $b$.

- arbitration (ar): an application specific, transitive and acyclic relation that
  provides a total order on conflicting
operations, ensuring that observed executions follow a single coherent timeline.

== Session Guarantees

In the implementation, the models follow the exact axiomatic definition provide
in Terry et al. @terry1994session and Viotti et al. @viotti2016consistency.
Below definitions are copied from the paper.

=== Monotonic Reads

Monotonic reads states that successive reads must reflect a non-decreasing set
of writes. Namely, if a process has read a certain value v from an object, any
successive read operation will not return any value written before v.
Intuitively, a read operation can be served only by those replicas that have
executed all write operations whose effects have already been observed by the
requesting process. In effect, we can represent this by saying that, given three
operations $a, b, c in H$, if $a arrow.long^"vis" b$ and
$b arrow.long^"so" c$, where $b$ and $c$ are read operations, then
$a arrow.long^"vis" c$, i.e., the transitive closure of vis and so is included
in vis.

$
  "MonotonicReads" eq.delta forall a in H, forall b, c in H_"rd": a arrow.long^"vis" b and b arrow.long^"so" c => a arrow.long^"vis" c
$

=== Monotonic Writes

In a system that ensures monotonic writes a write is only performed on a replica
if the replica has already performed all previous writes of the same session. In
other words, replicas shall apply all writes belonging to the same session
according to the order in which they were issued.

$
  "MonotonicWrites" eq.delta forall a, b in H_"wr": a arrow.long^"so" b => a arrow.long^"ar" b
$

=== Read Your Writes

Read-your-writes guarantee (also called read-my-writes) requires that a read
operation invoked by a process can only be carried out by replicas that have
already applied all writes previously invoked by the same process.

$
  "ReadYourWrites" eq.delta forall a in H_"wr", forall b in H_"rd": a arrow.long^"so" b => a arrow.long^"vis" b
$

=== Write Follows Read

Writes-follow-reads, sometimes called session causality, is somewhat the
converse concept of read-your-write guarantee as it ensures that writes made
during the session are ordered after any writes made by any process on any
object whose effects were seen by previous reads in the same session.

$
  "WriteFollowsRead" eq.delta forall a, c in H_"wr", forall b in H_"rd": a arrow.long^"vis" b and b arrow.long^"so" c => a arrow.long^"ar" c
$

== PRAM Consistency

Pipeline RAM (PRAM or FIFO) consistency prescribes that all processes see write
operations issued by a given process in the same order as they were invoked by
that process. On the other hand, processes may observe writes issued by
different processes in different orders. Thus, no global total ordering is
required. However, the writes from any given process (session) must be
serialized in order, as if they were in a pipeline - hence the name.

$
  "PRAM" eq.delta forall a, b in H: a arrow.long^"so" b => a arrow.long^"vis" b
$

== Causal Consistency

Our causal consistency is a combinition of Voitti et al. @viotti2016consistency
and causal memory @baldoni2002an extends beyond PRAM and session guarantees. The
*writes-into* relation @baldoni2002an links write operations directly to the
reads that return their values (at the same memory region). This ensures that if
a read observes a particular write, all subsequent writes in the same session
respect that causal ordering. Formally, it aligns session order (`so`),
arbitration (`ar`), visibility (`vis`), and writes-into (`wi`) to maintain
coherent causal histories.

To for operations to be in the `wi` set: a write `a` writes into a read `b` iff `b` returns
the value originally written by `a`, and `a`/`b` to reference the same object
(same memory region). There must be at most one `a` for each `b`, and `wi` is
acyclic.

If one operation follows another in session order, their relationship in the
abstract execution is further constrained. Specifically, if $(a, b) in "so"$,
then `a` must write-into `b` if `b` is a read, and `a` must be visible and
arbitrated before `b`. Thus, session order induces a causal ordering that is
reflected in the relations `wi`, `vis`, and `ar`.

// TODO: vis(a, b) -> (a, b) in "vis"
To incorporate session causility, we conjunct write-follow-reads with
writes-into set: if a read `b` observes a write `a` (i.e. `vis(a, b)`) and `b` is
followed by a write `c` in the same session (`so(b, c)`), then `ar(a, c)` ensures
that the causal dependency introduced by reading `a`'s value is respected by the
subsequent write `c`.

// TODO: need double check
$
  "Causal" eq.delta (forall a, b in H: (a, b) in "so" arrow.double (a, b) in "wi" sect "vis" sect "ar") and "WriteFollowsRead"
$

These conditions together ensure a causal memory model where session order,
observed values, and write sequences are all aligned, causally dependent writes
appear in the correct order from any observer's perspective.

== Liniearizability

Although linearizability is widely considered the gold standard for strong
consistency, our initial attempts resulted in a incomplete model. In our draft
encoding, we introduced a single global order to unify visibility and
arbitration for all write operations, and tried to enforce real-time ordering to
ensure that the observed histories comply with returns-before relations
(linearization as operations comes in instead of lazily ordering events when
reads occur @zhang2018building). However, the resulting formulas were too
restrictive and did not yield a complete model, as linearizability mandates a
very strong global ordering property that is non-trivial to capture in our
current axiomatic formulation.

= Semantic Comparison and Composition

A core contribution of our framework is the ability to reason not only about
individual consistency semantics in isolation but also about their pairwise
compatibility and compositional properties. This enables exploration of how
different models relate to each other and whether they can be combined to
produce stronger or more application-specific consistency guarantees.

We define compatibility between two consistency semantics $M_1$ and $M_2$ using
an implication-based criterion. $M_1$ is considered compatible with
$M_2$ if the formula $M_1 arrow.double M_2$ is valid, i.e., there is no
execution that satisfies all constraints of $M_1$ without also satisfying $M_2$.
We implement this by asserting the negation $not (M_1 arrow.double M_2)$ and
checking if it is unsatisfiable using our SMT-based approach. If no
counterexample can be found, it implies that $M_1$
refines/subsumes $M_2$. This compatibility check is not symmetric: $M_1 arrow.double M_2$
holding does not necessarily mean that $M_2 arrow.double M_1$ also holds.

To combine multiple consistency models into a single stronger model, we used
logical conjunctions on each model's constraints. By taking the constraints
representing each model's semantics and forming their conjunction, we derive a
composed model that enforces all included constraints simultaneously. Unlike
compatibility checks, where direction and implication matter, composition is
commutative-adding more models simply layers their constraints on top of one
another. This approach allows incremental composition, users can start from a
base model and iteratively strengthen it by adding new sets of constraints
(either from our implemented models or user-defined constraints) representing
additional consistency guarantees. For example, the conjunction of monotonic
reads, monotonic writes, and read-your-writes can yield PRAM consistency
@brzezinski2004session. Similarly, layering these and writes-follow-reads
recovers a form of causal consistency @perrin2016causal.

// see tests/test_composition.py for examples

= Modeling Real-World Applications

Beyond theoretical explorations, our framework also supports practical modeling
distributed applications that may rely on complex combinations of semantics.
Instead of checking at source code level tracing possible code paths like Noctua
@ma2024noctua with SMT solvers, our approach operates at axiomatic logic and
optionally application level, allowing researchers and system designers to
encode nodes (representing intermediate API endpoints or storage systems
providing consistency semantics) and edges (representing interactions or data
flows) within their systems. Each node may require or provide specific
consistency guarantees, while edges capture the ordering/visibility constraints
and optional application specific logics between events across services.

The `composable` function operates over a directed multigraph whose nodes and
edges represent services (nodes) and interactions (edges) in a distributed
system. Each node and edge can specify which consistency guarantees it needs or
provides in the form of constraints (e.g., monotonic reads, read-your-writes).

- *Nodes:* each node represents a logical component like services or storage
  systems, each node can:
  - Issue operations (e.g., read or write to shared state)
  - Require certain consistency properties (e.g., monotonic reads) for these
    operations
  - Provide certain consistency guarantees to downstream consumers

  In the current implementation, each node stores:
  - `name`: a unique identifier
  - `needs`: a set of constraints that must be satisfied to uphold the node's
    required semantics
  - `provs`: a set of constraints that characterize what the node provides to other
    nodes

- *Edges:* edges represent interactions or data flows between nodes, capturing:
  - Precedence constraints (e.g., write `a` must return before read `b` starts)
  - Required or optional additional constraints representing custom operations or
    relations that must hold between the source and destination nodes

The `composable` function attempts to find an assignment of constraints that
makes the entire graph "composable". In other words, it seeks a model in which
all nodes' `needs` can be matched with some nodes' `provs`, and all edges'
constraints are satisfied simultaneously. This corresponds to verifying if there
is a coherent assignment of semantics across the system's interactions. Users
may provide zero or more semantics to `needs` and `provs` for each node, and
similarly, zero or more constraints for each edge. During the check at each
level of the graph traversal, a *pairwise* check between source node `needs` in
conjunction of edge constraints against destination node `provs` is performed.
If the pairwise check is successful, all previous assignments are recorded and
used as context for further checks. In case of pairwise check failure
(contradiction), the function backtracks and selects other possible assignments
if there are more than one provide in each of the source
`needs`, edge constraints, and destination `provs`.

// TODO: do we need pseudocode here?

*Implementation:* given a starting node (conceptually, usually a client) and a
set of premise constraints, the function begins a DFS through the graph. At each
node:
- The function examines outgoing edges and their associated constraints.
- Each edge can impose conditions on the relationship between the source node's
  requirements (`needs`), the destination node's provided guarantees (`provs`),
  and any additional edge-specific constraints.
- The solver checks whether combining these constraints with the accumulated
  premise remains satisfiable.
If no consistent assignment is found for outgoing edges, the function
backtracks, exploring alternative paths or constraint combinations. During
traversal, the function uses the `compatible` checks behind the scenes. For each
candidate combination of node-level and edge-level constraints, it calls `compatible` to
ensure that no contradictions arise. If the DFS manages to visit all edges and
find consistent assignments for all node needs and provided constraints, the
function returns a `True` value along with a subgraph (`result`) that records a
satisfying assignment. The returned subgraph shows which edges and nodes were
selected and how their constraints were matched. If no satisfying assignment is
found, the function returns `False`, and `None` for the graph.

== Example: Online Shopping

Consider an online shop scenario where multiple services and components interact
to process customer interactions and purchases. The shop maintains an inventory
of products, and a shopping cart service, a transaction log to record purchases,
and the the client itself. Additionally, an arbitrator node to coordinate
interactions between the interactions between clients and the entire service
stack.

A customer uses a shopping cart service to preserve the state of the items they
intend to buy. The customer can read or write the cart's contents, adjusting
their intended purchases as they browse products. Let's say in this example,
clients do not care to see their latest update to the cart being propagated to
other devices immediately, but the states will eventually converge.

The shop holds the canonical inventory state. Before finalizing a purchase, the
customer's requested items must be checked against the shop's current inventory.
If items are available, the transaction can proceed, if not, the request fails
due to insufficient stock.

Once the shop confirms inventory, it records the customer's purchase in the
transaction log, and replicated across multiple nodes for fault tolerance.

An arbitrator acts as a gatekeeper that serializes requests and interacts with
both the shop (update inventory) and the transaction log (bookkeeping). When the
customer decides to make a purchase, the arbitrator:
+ Receives requests from client and write to a intermediate location (capturing
  the customer's intent)
+ Reads from the shop's inventory to verify item availability
+ If available, writes back to the shop to decrement the inventory and write and
  replicate the transaction to the log
+ If not available, reply back to the client with an error

The arbitrator or serialization point pattern is commonly used in other system
implementations like Paxos @lamport2001paxos to maintain a consistent order of
events at critial locations, ensuring that purchase requests are applied to the
shop and recorded in the transaction log in a well-defined sequence.

*Nodes:*
- *Arbitrator:* Provides linearizability
- *Tx:* Provides linearizability
- *Shop:* Provides RYW + MR, ensuring that once arbitrator updates inventory, all
  subsequent reads observe the writes
- *Client and Cart:* Represent endpoints that do not enforce any semantic by
  themselves but rely on the guarantees of the nodes they interact with

*Edges:*
- `Client` to `Cart` edge represent the customer adding items to their cart
- `Client` to `Shop` edge represent price checks or browsing inventory
- `Client` to `Arbitrator` edge represents a purchase request
- `Arbitrator` to `Shop` and `Arbitrator` to `Tx` edges represent the arbitrator's
  mediation: writing to the transaction log, reading and updating the shop's
  inventory state in sequential order

In this example, the `composable` function succeeds with a graph containing one
of the possible satisfiable constraint assignments.

== Example: Streaming Service

Another example (simplified from DeathStarBench Media Service @gan2019an):
consider a streaming service with multiple components handling user
authentication, content delivery, and user interactions. The system comprises:

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

As this example demonstrates, it's more complex than the online shopping mall
example. Listing of nodes and edges is not exhaustive, please see the actual
implementation for more details. The overall operational constraints are
captured through custom operation types with quantified constraints optionally
enforced at each node level.

// TODO: rewrite needed in the actual paper

== Example: Antipode @ferreira2023antipode

// TODO: rewrite after wrapping up
Basic encodings of lineage and cross-service causal consistency (XCY) are
finished but full implementation is still in progress. See `tests/test_antipode.py` for
details.