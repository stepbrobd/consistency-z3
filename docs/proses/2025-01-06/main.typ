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
  title: "Literature Review", authors: ((name: "Yifei Sun", email: "ysun@ccs.neu.edu"),), date: "January 10, 2024",
)

= Toward Domain-Specific Solvers for Distributed Consistency

== Summary

In Kuper et al. @kuper2019toward, the authors argued embedding automated theorem
solvers into a language like LiquidHaskell @vazou2014liquidhaskell and Rosette
@torlak2014a, and use these solver-aided languages implement distributed systems
can result in consistent-by-construction applications. However, transitive
relations, partial orderings, and external API invocations are difficult
properties to reason in these solver-aided languages due to non-trivial
encodings and efficiency concerns. The authors advocates for developing
domain-specific SMT solvers that are specialized for reasoning about distributed
consistency properties, and programmers should not need to fully understand
satisfiability modulo theories in order to implement theory solvers for their
domain of interest with the help of these domain-specific solver frameworks.

== Methodology

The paper presents a vision rather than a specific implementation, drawing on
experiences with existing systems to motivate the need for domain-specific
solvers. The methodology focuses on identifying key challenges and outlining a
research agenda rather than providing concrete solutions.

The authors listed three key features a "consistency-aware" solver should have:

- CRDT verifications: current verification of CRDT properties in Liquid Haskell
requires non-trivial encodings and takes up to 40 seconds for basic ordering
laws.

- Message reorderings: for lineage-driven fault injection (LDFI), the ability to
efficiently reason about message commutativity could enable exploration of bugs
triggered by message races while avoiding state explosion. Personally, this does
not seem to be a target area for our work.

- Transitive closures: in Quelea @sivaramakrishnan2015declarative, the inability
to precisely express transitive closure in first-order logic forces overly
conservative approximations of happens-before relationships. While this is a
very valid, and on-point concern, however, transitive closures are encodable in
solver frameworks with quantifiers elimination tactics and recursive definitions
(which are standards in SMT-LIB #footnote[https://smt-lib.org/papers/smt-lib-reference-v2.6-r2017-07-18.pdf].

== Relavance

On a first glance, the paper seem to reject our thesis where we did used
general-purpose SMT solvers like Z3 @demoura2008z3 to reason about distributed
consistency properties. Throughout the development of our framework, we have
encountered the same issues as the authors mentioned, where the encoding of
transitive relations, partial orderings, and non-deterministic operations are
non-trivial and inefficient.

However, rather than rejecting general-purpose solvers entirely, our work
demonstrates that careful encoding strategies and abstraction choices can help
mitigate some of these limitations. We take inspiration from the paper's vision
of domain-specific solvers while working within the constraints of existing
tools.

Instead of trying to deduce a global ordering of events from a set of axioms
(not decidable in the first place), we avoid explicit reasoning about state
machine transitions (i.e. explicit version vectors or Lamport clocks), our
framework treats consistency guarantees as logical constraints over abstract
executions. The checking call to solvers reduces verification to constraint
satisfaction problems (negation of implication) that are decidable in
first-order logic. However, we acknowledge that domain-specific solvers as
proposed could potentially make our approach even more efficient.

= Satisfiability Modulo Ordering Consistency Theory for SC, TSO, and PSO Memory Models

== Summary

Fan et al. @fan2023satisfiability propose a ordering consistency theory for
verifying multi-threaded programs under sequential consistency (SC), TSO and PSO
(total/partial store order) memory models. While partial orders can concisely
represent thread interleavings, existing approaches using integer difference
logic to encode ordering constraints are inefficient as they: compute exact
clock values when only relative ordering matters, and eagerly encode all
possible from-read orders (read-from and from-read are extramely similar to our
visible/visibility definition) regardless of whether they are needed. The
authors develop a theory solver that performs incremental consistency checking,
generates minimal conflict clauses, and includes specialized theory propagation.

== Methodology

The paper formalizes their ordering consistency theory $cal(T)"ord"$ with
signature where (Section 4.1):

$
  Sigma"ord" = { e_1, e_2, ..., attach(prec, br: "ppo"), attach(prec, br: "ws"), attach(prec, br: "rf"), attach(prec, br: "fr"), approx }
$

- $e_i$ are memory access events in $EE$
- $attach(prec, br: "ppo")$ represents preserved program order (binary predicate)
- $attach(prec, br: "ws")$ represents write serialization (binary predicate, total
  order of writes to same address)
- $attach(prec, br: "rf")$ represents read-from relation (binary predicate,
  linking writes to reads)
- $attach(prec, br: "fr")$ represents from-read relation (binary predicate,
  derived from $attach(prec, br: "ws")$ and $attach(prec, br: "rf")$)
- $approx$ represents atomicity equivalence relation

Where the 4 axioms of $cal(T)"ord"$ are:

- partial order where $attach(prec, br: "ws")$ only relates write events, $attach(prec, br: "rf")$ link
  write events to read events, and $attach(prec, br: "fr")$ link read events to
  write events
- equivalence relation (trivial reflexivity)
- from-read derivation where it's similar to our monotonic read definition
  (visibility included)
- consistency where $attach(prec, br: "ws") union attach(prec, br: "rf") union attach(prec, br: "fr")$ is
  consistent with $attach(prec, br: "ppo")$ and $approx$

The solver maintains an event graph (think of this as abstract executions) where
nodes are events and edges represent ordering relations. Rather than eagerly
encoding all possible from-read orders, it derives them on-demand during solving
when relevant variables are assigned. Consistency checking reduces to cycle
detection in this graph.

The solver performs incremental cycle detection by maintaining a
pseudo-topological order of events and updating it efficiently when edges are
added. When inconsistency is detected, it generates minimal conflict clauses by
finding critical cycles with the smallest number of induced edges. This
formalization aligns closely with our visibility/visible definitions (and
session semantic definitions), but they treat read-from and from-read as
separate relations rather than doing explicit case analysis and combining them
into a single visibility relation.

== Relavance

The paper's formalization approach provides important insights for our work.
Their rigorous axiomatization of ordering relations provides a template for how
we could formalize our consistency models more precisely (instead of using
proses like how we have).

While we focused on higher-level consistency specifications rather than
low-level memory model semantics, and considering we combined read-from and
from-read into a single visibility relation with case analysis rather than
treating them separately, this paper demonstrates the benefits of having a
precise formal theory with clear axioms and efficient decision procedures. Even
though the domain is different, many of their theoretical techniques could
potentially be adapted to make our framework more rigorous and efficient.

Couple points to note: we should take their pseudocode example and layout our
checking logic. They also made Fig. 3 to demonstrate the differences of event
graphs constructed from different relations, we should also consider this to
show the case analysis for visibility definition For application level checking,
Fig. 5 and Fig. 6 should be taken into consideration, and we should implement
SMT-LIB exporter to make our tool checker agnostic. The paper also have
experiments on evaluations, we should also consider this.

= Bibliography

#bibliography(
  "bibliography.yml", title: none, style: "association-for-computing-machinery",
)
