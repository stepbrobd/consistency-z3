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

@fan2023satisfiability

== Relavance

== Methodology

= Bibliography

#bibliography(
  "bibliography.yml", title: none, style: "association-for-computing-machinery",
)
