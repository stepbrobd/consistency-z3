#import "@preview/polylux:0.3.1": *
#import themes.simple: *

#let title = "Safety Properties of Session Guarantees"
#let author = "Yifei Sun"
#let date = datetime(year: 2024, month: 1, day: 24)

#set document(title: title, author: author, date: date)
#set page(paper: "presentation-16-9")

#show: simple-theme.with(footer: none)

#title-slide[
  = #title
  #v(4em)

  #author

  #date.display("[month repr:long] [day padding:none], [year]")
]

#slide[
  == Base

  ${P} C {Q}$

  ${P}$: initial state (an empty history + set of assertions) // assertions includes constraint premitives (rb, ss, etc.) and conflic resolution tactics

  $C$: program // axiomatic semantics

  ${Q}$: eventual convergence (or $C$ might never terminate) // all replicas eventually reach the same state
]

#slide[
== Premitives

```py
  OperationType = z3.EnumSort("OperationType", ["rd", "wr"])
  Operation.declare("cons",
    ("proc", z3.IntSort()),    # process id
    ("type", OperationType),   # operation type
    ("obj", z3.IntSort()),     # invoking object
    ("ival", z3.StringSort()), # input value
    ("oval", z3.StringSort()), # output value
    ("stime", z3.IntSort()),   # start time
    ("rtime", z3.IntSort())    # return time
  )
  ```
]

#slide[
  == Premitives

  $"rb" eq.delta {("a","b"): "a","b" in "H" and "a.rtime" < "b.stime"}$ @viotti2016consistency

  $"ss" eq.delta {("a","b"): "a","b" in "H" and "a.proc" = "b.proc"}$ @viotti2016consistency

  $"so" eq.delta "rb" sect "ss"$ @viotti2016consistency
]

#slide[
  == Premitives

  // AT is acyclicity constraints, TP is transitivity constraints

  vis: $"visibility" and "AC" and "TC"$
  // if a -vis> b, all writes before a.rtime (including a if a.type = wr) are visible to b
  // and all reads afer b.stime (including b if b.type = rd) in b.proc

  ar: strict total order (for conflic resolution) // no self comparison (not a < a)
  // if a > b then not b > a
  // if a > b and b > c then a > c
  // if a !=b then either a > b or b > a

  \* Need rework, in current representation, both vis and ar are modeled as
  $"rb" and "AC" and "TC"$
]

#slide[
  == Example

  https://github.com/stepbrobd/consistency#example
]

#slide[
  == Models

  - Monotonic Reads
  - Monotonic Writes
  - Read Your Writes
  - Writes Follow Reads
  - PRAM Consistency
]

#slide[
== Results

Satisfiability of models:

```txt
  MonotonicReads: True
  MonotonicWrites: True
  PRAMConsistency: True
  ReadYourWrites: True
  WritesFollowReads: True
  ```
]

#slide[
== Results

// check LHS and RHS, whether all assertions in RHS can be satisfied in LHS under all possible assignments
Pairwise validity (check whether $not ("LHS" arrow.r.double "RHS") eq.triple "LHS" and not "RHS"$ is
unsatisfiable or not):

```txt
  MonotonicReads <- MonotonicWrites: False
  MonotonicReads <- PRAMConsistency: False
  MonotonicReads <- ReadYourWrites: False
  MonotonicReads <- WritesFollowReads: False
  MonotonicWrites <- MonotonicReads: False
  MonotonicWrites <- PRAMConsistency: False
  MonotonicWrites <- ReadYourWrites: False
  MonotonicWrites <- WritesFollowReads: False
  PRAMConsistency <- MonotonicReads: True
  PRAMConsistency <- MonotonicWrites: False
  PRAMConsistency <- ReadYourWrites: True
  PRAMConsistency <- WritesFollowReads: False
  ReadYourWrites <- MonotonicReads: False
  ReadYourWrites <- MonotonicWrites: False
  ReadYourWrites <- PRAMConsistency: False
  ReadYourWrites <- WritesFollowReads: False
  WritesFollowReads <- MonotonicReads: False
  WritesFollowReads <- MonotonicWrites: False
  WritesFollowReads <- PRAMConsistency: False
  WritesFollowReads <- ReadYourWrites: False
  ```
]

#slide[
== Results

// take the result of the conjunction, then check pairwise validity
Composition (conjunction of assertions):

```txt
  PRAM <- {RYW, MR, MW}: False
  {RYW, MR, MW} <- PRAM: False
  PRAM <- {MR, RYW}: True
  {MR, RYW} <- PRAM: False
  ```
]

#slide[
  == References

  #bibliography("bibliography.yml", title: none, style: "ieee")
]
