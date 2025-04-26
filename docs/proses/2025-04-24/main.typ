#import "diagbox.typ": *

#let doc(title: "", authors: (), date: none, body) = {
  set document(author: authors.map(a => a.name), title: title)
  set page(numbering: "1", number-align: center)

  align(center)[#block(text(weight: 700, 1.75em, title))]

  pad(
    top: 0.5em, bottom: 0.5em, x: 2em, grid(
      columns: (1fr,) * calc.min(3, authors.len()), gutter: 1em, ..authors.map(author => align(center)[
        *#author.name* \
        #author.email
      ]),
    ),
  )

  align(center)[#date]

  set par(justify: true)

  body
}

#show: doc.with(
  title: "CS 8674 Project Report", authors: ((name: "Yifei Sun", email: "ysun@ccs.neu.edu"),), date: "April 26, 2025",
)

= Introduction

Modern distributed systems often relax strict consistency guarantees to achieve
scalability, fault tolerance, and low latency operations. Understanding and
comparing different forms of relaxed consistency semantics is crucial for both
system designers and researchers. Yet, systematically modeling and reasoning
about these semantics, as well as their compositional properties, remained a
understudied area.

Our framework aims to bridge this gap by providing a SMT-based approach to
encode and analyze the safety properties of weaker consistency models (comparing
with linearizability @herlihy1990linearizability), and their compositions under
the assumption of livenss properties are always satisfied, i.e. eventual
consistency @petersen1997flexible is guaranteed (replicas eventually converge),
and we are layering everything on top of it. By offering a per-system
(differentiated by symbols), logical representation of operations, our system
can differentiates operations belonging to distinct systems and/or components
through the use of unique symbols (see tests/test_cross_causal.py), enabling
analysis of cross-system interactions. Additionally, solver backends can
discharge proof witnesses on the satisfiability of specific consistency
properties, or the compatibility and composability between multiple models.
These approaches enable fast exploration and iteration of alternative system
designs, guiding the development adhere to intended consistency guarantees from
the very beginning.

// TODO: rewrite after wrapping up

= Terminology

// when writing the actual paper, explanations below should be moved to pseudocode

- Operations: Modeled as an extensible tuples (proc, type, obj, ival, oval, stime,
  rtime) @viotti2016consistency representing atomic actions in the system.
  Additional fields can be added by invoking the sort constructor with additional
  fields.

- Axioms/Relations: Predicate logic constraints defined over operations.
  - History Relations: Deterministic orderings based on time and session
    (returns-before, same-session, session-order, etc.).
  - Abstract Execution Relations: Non-deterministic orderings capturing more complex
    temporal constraints and conflict resolution (visibility, arbitration,
    happens-before, etc.).

- Consistency Semantics/Models: Specific consistency guarantees defined as logical
  formulas over axioms/relations (e.g., Monotonic Reads, PRAM, Causal Consistency,
  etc.). Each model enforces safety properties i.e. specific ordering and
  visibility constraints on operations within history and abstract executions.

- Functions on Models:
  - Compatibility Check (`compatible(lhs, rhs)`): Determines if one set of
    constraints (lhs) implies another set of constraints (rhs) under a given
    background context (others and global Relation.Constraints()). This function
    uses the construct helper function to create a Z3 solver instance. construct
    asserts the negation of the implication: Not(Implies(lhs, rhs)). This is
    logically equivalent to lhs And Not(rhs). It also adds the background
    constraints (others and Relation.Constraints()). The compatible function then
    calls s.check() on this solver. If s.check() returns z3.unsat (unsatisfiable),
    it means there is no model (no counterexample) where lhs is true and rhs is
    false. Therefore, whenever lhs holds, rhs must also hold. The function returns
    True (compatible). If s.check() returns z3.sat (satisfiable), it means a
    counterexample exists, the implication does not hold universally, and the
    function returns False (not compatible).

  - Composability Check (`composable(graph, src, ...)`): Verifies if a distributed
    system, modeled as a graph (`graph: nx.MultiDiGraph`), can have its components
    interact in a way that respects their individual consistency requirements and
    guarantees. The function checks if there exists at least one valid way to assign
    specific semantics (from the choices provided in needs/provs/cons) such that all
    interactions are consistent. The graph in the function parameter composed by
    Nodes (`Node`) with needs (list of required semantic tuples) and provs (list of
    provided semantic tuples). Edges (`Edge`) connect nodes and can have cons (list
    of semantic tuples constraining the interaction). Lists represent alternative
    choices (logical or), while tuples within the list represent constraints that
    must hold together (logical and). In the implementation, we perform a
    Depth-First Search (DFS) starting from a given source node, keeping track of
    visited edges and the accumulated constraints (`path_premise`) along the current
    path. For each unvisited edge (u,v) from the current node u: It iterates through
    all combinations (product) of possible needs from u, provs from v, and cons from
    the edge (u, v). For each combination, it performs a compatible check: `compatible(check_provs, compose(check_needs, check_ec), path_premise)`.
    This checks if the chosen provides guarantee of the destination (check_provs) is
    implied by the conjunction (compose) of the chosen needs of the source
    (check_needs) and the chosen edge constraints (check_ec), considering the
    constraints already accumulated (path_premise). If a compatible combination is
    found that satisfies all unvisited edges between u and v at the current step,
    it: Adds the chosen constraints (needs, provs, cons) to the result graph.
    Updates the path_premise by composing the newly satisfied constraints. Marks the
    edges as visited. Continues the DFS from the destination node v. If the DFS
    eventually visits all edges in the graph, the function returns True and the
    result graph showing one valid assignment. If a dead end is reached or no
    compatible combination works for an edge, it backtracks, removing the choices
    made at that step and trying other combinations. If the DFS completes without
    visiting all edges (meaning no fully consistent assignment was found), it
    returns False.

  - Extraction (`extract(inode, onode, result)`): After a successful composable
    check, this function takes the resulting graph from composability check (which
    represents ONE valid assignment of constraints) and aggregate a single Z3
    constraint (z3.AstRef) that represents the net or equivalent semantic guarantee
    of the subgraph reachable from a specific node (inode), assuming inode and onode
    are the same. The function performs a DFS (dfs helper) starting from the
    specified inode on this result graph. For each edge (src, dst) traversed in the
    DFS, extraction function uses the specific provs constraint assigned to src in
    the result graph, uses the specific needs constraint assigned to dst in the
    result graph, and retrieves the specific cons constraint assigned to the edge
    (src, dst, k) in the result graph. The extract function will create a composite
    constraint for this single edge interaction: compose(src_provs, edge_cons,
    dst_needs). This represents the conjunction of constraints relevant to this
    specific step in the flow. It collects these composite constraints from all
    edges reachable from inode in the DFS. Finally, it returns the logical and
    (compose) of all collected composite constraints. Simply put, axioms/relations
    define constraints on Operations, similarly, extract defines a summary
    constraint on a successfully composed subgraph. If the composable check found a
    valid way for components A, B, and C to interact starting from A, extract(A, A,
    result) generates a single formula representing the overall guarantee provided
    by the A->B->C... chain, as seen from A's perspective, based on the specific
    choices made during the composability check.

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
across multiple nodes need to be modeled separately on different set of symbols
to avoid conflicts in quantified variables. Further, to reason about cross
system behaviors, "glue" constraints need to be added to represent data flow
between different systems.

== Operations

To capture behaviors in distributed system executions, we model state
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

When modeling multiple interacting systems or components within a single
analysis context, using distinct symbols for the operations belonging to each
system is crucial. Consistency semantics are typically defined using universally
quantified formulas (e.g., $forall a, b: dots$) applied to relations treated as
uninterpreted functions by the SMT solver (e.g., $"vis"(a, b)$, $"so"(a, b)$).
If the same symbolic operations (like $a, b$) and relation functions (like $"vis"$)
were reused across the models of different systems within the same solver query,
the solver would treat them as the *same* entities. This could lead to
unintended interactions and logical conflicts: constraints from one system's
model might implicitly and incorrectly restrict the behavior of operations
logically belonging to another system. By assigning unique symbols to operations
(and potentially relations) associated with different components (e.g., $a_X$, $b_X$, $"vis"_X$ for
System X; $a_Y$, $b_Y$, $"vis"_Y$ for System Y), we maintain the necessary
logical isolation. This ensures that the axioms and constraints of a specific
consistency model only apply to the operations within that specific system's
scope. This symbolic separation is fundamental for enabling the analysis of
*cross-system* interactions, where specific "glue" constraints can then be added
explicitly to relate operations across these distinct symbolic domains, as
demonstrated in our cross-causal consistency modeling.

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

- session-order: $"so" eq.delta "rb" inter "ss"$

- same-object: $"ob" eq.delta {(a, b) : a, b in H and a."obj" = b."obj"}$

In our implementation, each history relation function (e.g., `History.Relation.returns_before`)
accepts an optional `symbols` argument. This parameter allows framework users to
explicitly specify the symbolic operations (e.g., `["a_X", "b_X"]`) over which
the relation's constraints should be quantified for that specific instance. This
mechanism enables the application of history-based constraints distinctly to
operations belonging to different modeled systems or components, contributing to
the logical isolation necessary for cross-system analysis. If the `symbols` argument
is omitted, the functions default to a standard set of symbols (like `["a", "b"]`),
applying the constraints to a general set of operations suitable for
single-system analysis.

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

Similar to History relations, the Abstract Execution relation functions in our
implementation (e.g., `AbstractExecution.Relation.visibility`) also accept an
optional `symbols` argument. This allows framework users to instantiate AE
relations with constraints quantified over specific symbolic operations relevant
to a particular system or component being modeled. Omitting the argument applies
the relation to the default set of symbols.

Axioms defined for operations within abstract executions:

- visibility (vis): visibility definition used in all literatures we've reviewed
  are ambiguous in the sense that they don't specify the exact behavior under
  concurrent settings @viotti2016consistency @viotti2016towards @zhang2018building
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
+ write-read: $"viewed" inter "ar"$, simply viewed (value equivalence) +
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
  provides a total order on conflicting operations, ensuring that observed
  executions follow a single coherent timeline.

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
  "Causal" eq.delta (forall a, b in H: (a, b) in "so" arrow.double (a, b) in "wi" inter "vis" inter "ar") and "WriteFollowsRead"
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

= Reasoning about Consistency Semantics

While the previous sections define individual consistency semantics (like
Monotonic Reads, PRAM, Causal Consistency) and the underlying axioms, this
section explains how these elements are used within the framework for analysis,
particularly concerning the use of symbols and the modeling of interacting
systems.

// reasning individual semantics and pairwise compatibility

When analyzing a single consistency model in isolation (e.g., checking its
satisfiability via `check()`) or comparing two models directly (e.g., checking
if $M_1$ implies $M_2$ via `compatible(M1, M2)`), it is typically sufficient and
standard practice within the framework to use the default set of operation
symbols (e.g., $a, b, c$). In these contexts, the analysis focuses on the
inherent logical properties and relationships defined by the models' axioms
themselves, abstracted away from any specific, larger system implementation. The
goal is to understand the theoretical guarantees provided by a model or the
logical relationship between two different models.

// modeling composite systems with distinct symbols

However, the framework is designed with the expectation that users will model
larger distributed systems composed of multiple distinct components (e.g.,
different microservices, databases, caches), each potentially providing
different consistency guarantees. As established in the "Operations" section,
modeling these distinct components within the same analysis requires logical
isolation to prevent unintended interference between their constraints.

Our framework achieves this isolation by allowing *instantiation* of consistency
models and their underlying relations (both History and Abstract Execution)
using unique symbols for each component. All model definition methods (e.g., `MonotonicReads.assertions`)
and relation methods (e.g., `History.Relation.session_order`, `AbstractExecution.Relation.visibility`)
accept an optional `symbols` parameter. By passing distinct lists of symbols
when defining the `needs` or `provs` constraints for different nodes in a system
graph, users ensure that the constraints for, say, System X (using symbols $a_X, b_X, dots$)
are kept separate from those of System Y (using symbols $a_Y, b_Y, dots$) within
the SMT solver's context. This explicit symbolic differentiation is essential
for correctly modeling the behavior of individual components within a larger
architecture, as demonstrated in `tests/test_cross_causal.py`.

// what are glue constraints

Modeling components with distinct symbols provides necessary isolation, but to
analyze the behavior of the *composite* system, we must model the interactions
*between* these components. This is achieved through "glue" constraints:
explicit logical formulas that relate operations across different symbolic
domains.

In the context of the `composable` function, these glue constraints are
typically added to the `cons` attribute of the `Edge` connecting the two
components being modeled. They represent the real-world dependencies or data
flows that bridge the conceptual boundary between the isolated components.
Examples of what glue constraints can model include:

- *Data Flow*: An operation $a_X$ in System X produces data consumed by $b_Y$ in
  System Y:
  $
    a_X."oval" = b_Y."ival"
  $
- *Causal Ordering*: Application logic dictates that the completion of $a_X$ must
  happen before $b_Y$ starts:
  $
    a_X."rtime" < b_Y."stime" \
    #text(" (or potentially a stronger cross-system happens-before relation)")
  $
- *Serialization/API Gateway*: An intermediate component (like an API gateway or
  arbitrator modeled implicitly by the edge constraint) serializes operations $a_X$ and $b_Y$ (note
  that the default arbitration constraint enfoces a very strong serial ordering,
  to model real-world use cases, users may need to override the provided
  definition):
  $
    "ar"_"gateway"(a_X, b_Y) \
    #text(" (using a specific arbitration relation for the gateway)")
  $

These glue constraints are essential for a meaningful analysis of the composite
system. Without them, the components would remain logically isolated, and the
analysis could not capture potential violations or emergent behaviors arising
from their interactions. The nature of these constraints can range from weak
(e.g., simple temporal ordering) to strong (e.g., requiring value equality or
specific causal links), depending on the semantics of the interaction being
modeled.

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

#let table_na = bdiagbox(width: 2.275cm, height: 0.73cm)[][]
#let table_t = [#text(green)[T]]
#let table_f = [#text(red)[F]]
#table(
  columns: (auto, auto, auto, auto, auto, auto, auto), bdiagbox(width: 2.275cm, height: 1.25cm)[*LHS*][*RHS*], [*PRAM*], [*Monotonic Reads*], [*Monotonic Writes*], [*Read Your Writes*], [*Writes Follow Reads*], [*Lineariza-bility*], [*PRAM*], [#table_na], [#table_t], [#table_t], [#table_t], [#table_f], [#table_f], [*Monotonic Reads*], [#table_f], [#table_na], [#table_f], [#table_f], [#table_f], [#table_f], [*Monotonic Writes*], [#table_f], [#table_f], [#table_na], [#table_f], [#table_f], [#table_f], [*Read Your Writes*], [#table_f], [#table_f], [#table_f], [#table_na], [#table_f], [#table_f], [*Writes Follow Reads*], [#table_f], [#table_f], [#table_f], [#table_f], bdiagbox(width: 2.3cm, height: 1.25cm)[][], [#table_f], [*Lineariza-bility*], [#table_t], [#table_t], [#table_t], [#table_t], [#table_t], bdiagbox(width: 2.3cm, height: 1.25cm)[][],
)

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

/* antipode no more :<
// TODO: rewrite needed in the actual paper

== Example: Antipode @ferreira2023antipode

// TODO: rewrite after wrapping up
Basic encodings of lineage and cross-service causal consistency (XCY) are
finished but full implementation is still in progress. See `tests/test_antipode.py` for
details.
*/

== Example: Cross Service Causal

When reading the graph, think of it as a reversed tree (rooted from svc1) with
one branch growing from root to leaf (xc). The leaf node's (xc) prov/need field
in the implementation is set to `None` to indicate that it does not provide any
guarantees, and will only be used for extraction (see descriptions below).
Implementation of `tests/test_cross_causal.py`:

```txt
            xc
           / <- mr + mw + ryw
        svc4 - wfr
       / <- mr + mw + wfr
     svc3 - ryw
    / <- mr + ryw + wfr
  svc2 - mw
 / <- mw + ryw + wfr
svc1 - mr
```

This example demonstrates modeling a system where multiple services, each
offering only a basic consistency guarantee, are chained together. The goal is
to verify if their composition, mediated by specific inter-service constraints,
symbolic isolation, and the role of explicit "glue" constraints.

*Setup #footnote(
  "I decided not to use the \"pseudo node\" in the write up, it makes the explanation unnecessarily complex.",
):* We model a linear chain of services: $"SVC1" -> "SVC2" -> "SVC3" -> "SVC4" -> "XC"$.
Each service $"SVC"n$ (for $n=1..4$) is designed to provide only *one* of the
four session guarantees via its `provs` attribute: $"SVC"1$ provides MR, $"SVC"2$ provides
MW, $"SVC"3$ provides RYW, and $"SVC"4$ provides WFR.

*Symbolic Isolation:* To prevent logical interference, the guarantee provided by
each service (e.g., `MonotonicReads.assertions`) and the constraints added on
the edges are instantiated using unique symbols specific to that service or edge
(e.g., using helpers like `gensym` and `assertion_for` from `tests/test_cross_causal.py`).
This ensures, for example, that the Monotonic Reads constraints of $"SVC"1$ only
apply to operations symbolically designated as belonging to $"SVC"1$.

*Composition via Edge Constraints:* The composition logic resides in the "glue"
constraints defined on the `cons` attribute of the edges connecting the
services. Since each service node only provides one session guarantee, the edge $"SVC"n -> "SVC"(n+1)$ must
provide constraints representing the other three session guarantees needed to
potentially satisfy Causal Consistency up to that point.

The core idea of this example is to build a stronger guarantee by composing
weaker guarantees provided by individual services ($"SVC"1 dots 4$), using the
edges to supply the missing pieces. Verbatim:

- $"SVC"1$ starts by providing only MR (via its `provs`, using symbols like $a_1, b_1, dots$).
  Its own `needs` are `None`.
- To potentially achieve Causal Consistency for operations passing from $"SVC"1$ to $"SVC"2$,
  the edge $"Edge"("SVC1" -> "SVC2")$ must provide the other three required
  session guarantees: MW, RYW, and WFR (via its `cons`, using unique symbols like $a_{12}, b_{12}, dots$).
  However, in real world implementations, edge constraints usually requires
  additional application specific logic to be satisfiable. In other word, edge
  constraints used in abstract representation implies the existence of application
  level protocols that enforces convergence of data either through consensus (like
  Raft @diego2014raft or Paxos @lamport1998paxos) or other means.
- When `composable` evaluates this step, it checks if the interaction is locally
  consistent based on the nodes' defined `provs`/`needs` and the edge's `cons`. If
  this local check passes (meaning $"SVC"2$'s required guarantee, Causal
  Consistency, is satisfied through what the edge + $"SVC"1$'s provs provide), we
  *interpret* this (based on our setup) as achieving Causal Consistency for the
  combined path ($"SVC"1 + "Edge"("SVC1" -> "SVC2")$) leading *up to* $"SVC"2$.
- Now, although the path leading to $"SVC"2$ is causally consistent, $"SVC"2$ itself,
  according to its definition in this example, only *provides* MW to the outside
  world (via its `provs`, using symbols $a_2, b_2, dots$).
- Therefore, for the *next* service, $"SVC"3$, to maintain Causal Consistency
  relative to the operations flowing through the ($"SVC"1->"SVC"2$) mesh, the edge $"Edge"("SVC2" -> "SVC3")$ must
  supply the guarantees missing relative to $"SVC"2$'s provided MW. This means $"Edge"("SVC2" -> "SVC3")$ must
  provide MR, RYW, and WFR (again, with unique symbols).
- This pattern repeats: each service node $"SVC"n$ provides one specific
  guarantee, and the edge $"Edge"(n -> n+1)$ provides the complementary guarantees
  needed to ensure the cumulative path maintains the target property.

*Symbol Equivalence:* For this composition to be meaningful, we must
conceptually link operations across services that refer to the same logical
action or data. For instance, if write $a_1$ in $"SVC"1$ and write $a_2$ in $"SVC"2$ both
represent updates to the same user profile, "glue" constraints equating relevant
aspects (like $a_1."obj" = a_2."obj"$ or $a_1."ival" = a_2."ival"$ despite their
different symbolic names) might be necessary. While the current test code (`tests/test_cross_causal.py`)
simplifies this by focusing on composing the consistency axioms, a more rigorous
model would include these explicit symbol equivalence constraints on the edges
(we are directly asserting symbols of $a_1$ are identical of those of $a_2$ for
simplicity).

*Aggregation:* The `composable(g, svc1)` call attempts to find a satisfying
assignment for the entire chain, respecting the `provs` of each node and the `cons` of
each edge. If it returns `True`, it confirms that the individual guarantees can
be composed under the specified edge constraints. Subsequently, `extract(svc1, svc1, (ok, res))` can
synthesize a single logical formula representing the net end-to-end guarantee
achieved by the chain, starting from $"SVC"1$. This aggregated constraint (`aggcons` in
the test code) could then be compared against a formal definition of Causal
Consistency.

= Artifact Evaluation

Software required: Nix, all dependencies locked with Nix

Steps:

- Install Nix
  - On your own machine: https://nixos.org/download/#download-nix
  - Or use Nix Docker image: `docker pull nixos/nix` and `docker run -it nixos/nix`

- Get the code:

  ```sh
    nix –-extra-experimental-features "flakes nix-command" run nixpkgs#git -- clone https://github.com/stepbrobd/consistency-z3.git`
    cd consistency-z3
    ```

- Get dependencies: `nix –-extra-experimental-features "flakes nix-command" develop -c $SHELL` (required)
  - After this step, you should be automatically dropped in a virtual environment
    managed by UV, and all dependencies should be installed

- Run tests: `uv run pytest` in the root directory of the project

- If you want to make new tests, add a new test file in `tests/` directory, follow
  setups of existing tests, and run `uv run pytest ./tests/<your file>.py` (command
  line parsing not done yet)

= Bibliography

#bibliography(
  "bibliography.yml", title: none, style: "association-for-computing-machinery",
)
