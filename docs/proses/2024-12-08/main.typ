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
  title: "CS 8674 Project Report", authors: ((name: "Yifei Sun", email: "ysun@ccs.neu.edu"),), date: "December 11, 2024",
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

== Axioms

/*
* Relation predicates:
* A set of predicates that define the relations between operations in a history (also includes those in AE).
* The predicates are used as base/premise for consistency models (implementations in relation.py, history.py, abstract_execution.py). In the implementation, the predicates are singletons and will be added ad-hoc if any clause refers to them.
*/

Axioms are relations defined over operations. These relations are declared as
uninterpreted functions, where the SMT solvers are free to interpret them so
long as they satisfy the imposed constraints.

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

// TODO: add descriptions

- returns-before: $"rb" eq.delta {(a, b) : a, b in H and a."rtime" < b."stime"}$

- same-session: $"ss" eq.delta {(a, b) : a, b in H and a."proc" = b."proc"}$

- session-order: $"so" eq.delta {(a, b) : a, b in H and "rb" sect "ss"}$

- same-object: $"ob" eq.delta {(a, b) : a, b in H and a."obj" = b."obj"}$

=== Abstract Execution

== Session Guarantees

=== Monotonic Reads
//
=== Monotonic Writes

=== Read Your Writes

=== Write Follows Read

== PRAM Consistency

== Causal Consistency

= Semantic Composition

= Modeling Real-World Applications

= Bibliography

#bibliography(
  "bibliography.yml", title: none, style: "association-for-computing-machinery",
)
