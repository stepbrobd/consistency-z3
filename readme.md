# Consistency

[![Built with Nix](https://builtwithnix.org/badge.svg)](https://builtwithnix.org)

> [!Caution]
> Experimental project, use at your own risk.

Binary Cache:

- Cache: <https://cache.ysun.co>
- Key: `cache.ysun.co-1:WxPYwT5g3kt9XhUhHPpNLZKI9HIOsVVAuqSHpok8Qt4=`

## Usage

Our original plan was to designa CLI tool, but due to time constraints, this
tool can only be used as a library. Either install with `pip` or make a new
`pytest` module under the `tests` directory to start immediately.

Some examples might take a very long time to run, so we recommend using the
`not slow` marker to skip those tests when trying to do artifact evaluation.

```sh
pytest --cov=consistency tests -sm 'not slow'
```

Nix is requried to do the artifact evaluation. Please use the official Nix
installer <https://nixos.org/download> or DetSys Nix installer
<https://github.com/determinatesystems/nix-installer> to get started.

After installing Nix, simply run:

```sh
nix develop -c $SHELL
```

to get all dependencies installed and the environment set up (might take a while
the first time).

To run specific tests, use the `-sk` option print test outputs. For example:

```sh
pytest -sk test_timing_xc
```

For timing tests you will need to use the watchdog script to ensure Z3 timeouts
are handled correctly:

```sh
# run the test first, and record the output path printed in the first couple lines
pytest -sk test_timing_media
# get the pytest PID for monitoring
ps -ax | grep pytest
# run the watchdog script with root privileges
sudo python ./scripts/watchdog.py <PID>
```

Results can be reproduced by running the analysis script with the:

```sh
# replace the file paths first
python scripts/analyze.py
```

## Guidelines

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

### Linearizability

[`consistency/model/linearizability.py`](consistency/model/linearizability.py)

Liniearizability is a conjunction between Single Order, Real Time and Return
Value consistency (pp. 5). Single Order imposes a single global order that
defines both visibility and arbitration (very strong, probably can't be
modeled), whereas Real Time constrains arbitration to comply to the
returns-before partial ordering. Finally, Return Value consistency specifies the
return value consistency of a replicated data type.

### Causal Consistency

[`consistency/model/causal_consistency.py`](consistency/model/causal_consistency.py)

Our modified version of causal consistency.

```math
Causal \triangleq \text{WFR} \land \forall a, b \in H: (a, b) \in \text{so} \Rightarrow (a, b) \in \text{wi} \cap \text{vis} \cap \text{ar}
```

### PRAM Consistency

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

### Monotonic Reads

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

### Read Your Writes

[`consistency/model/read_your_writes.py`](consistency/model/read_your_writes.py)
and [`consistency/model/read_my_writes.py`](consistency/model/read_my_writes.py)

Read-your-writes guarantee (also called read-my-writes) requires that a read
operation invoked by a process can only be carried out by replicas that have
already applied all writes previously invoked by the same process.

```math
ReadYourWrites \triangleq \forall a \in H|_{wr}, \forall b \in H|_{rd}: a\overset{so}{\rightarrow} b \Rightarrow a \overset{vis}{\rightarrow} b \triangleq so|_{wr \rightarrow rd} \subseteq vis
```

### Monotonic Writes

[`consistency/model/monotonic_writes.py`](consistency/model/monotonic_writes.py)

In a system that ensures monotonic writes a write is only performed on a replica
if the replica has already performed all previous writes of the same session. In
other words, replicas shall apply all writes belonging to the same session
according to the order in which they were issued.

```math
MonotonicWrites \triangleq \forall a, b \in H_{wr}: a\overset{so}{\rightarrow} b \Rightarrow a \overset{ar}{\rightarrow} b \triangleq so|_{wr \rightarrow wr} \subseteq ar
```

### Writes Follow Reads

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

### Eventual Consistency

[`consistency/model/eventual_consistency.py`](consistency/model/eventual_consistency.py)

Eventual without liveness.

```math
Eventual(\mathcal{F}) \triangleq \text{acyclic}(hb) \land \forall op \in H: op.oval \in \mathcal{F}(op, ctx(A, op)) \mathcal{F}_{\text{can-view}}(op, ctx(A, op)) = \{x.ival \in H_\text{wr} : (op, x) \in \text{can-view}\}
```

### Parameterized RVAL

[`consistency/model/rval.py`](consistency/model/rval.py)

Context dependent, see implementation for details.

## License

The contents inside this repository, excluding all submodules, are licensed
under the [MIT License](license.md). Third-party file(s) and/or code(s) are
subject to their original term(s) and/or license(s).
