#import "@preview/polylux:0.3.1": *
#import themes.simple: *

#let title = "Reasoning about\nCompositional Consistency Semantics"
#let author = "Yifei Sun"
#let date = datetime(year: 2024, month: 3, day: 20)

#set document(title: title, author: author, date: date)
#set page(paper: "presentation-16-9")

#show: simple-theme.with(footer: none)

#title-slide[
  = #title
  #v(4em)

  #author

  #date.display("[month repr:long] [day padding:none], [year]")
]

#pagebreak()

#side-by-side[
  == Session Guarantees

  "... either the storage system ensures them for each read and write operation
  belonging to a session, or else it informs the calling application that the
  guarantee cannot be met." @terry1994session
][
```txt
  client <--(1)-- cart
  ^
  |
 (1)
  |
  |
  shop --- arbitrator --- tx
  ```

(1): Storage systems should provide guarantees to all read and write operations
within a session.
]

#pagebreak()

#side-by-side[
  == Session Guarantees

  $"C" := {emptyset}$

  $"S" := PP({"RYW", "MR", "WFR", "MW"})$

  $"f"("C", "S") == "SAT"$

  $"f"("LHS", "RHS") eq.delta not (exists l in "LHS", exists r in "RHS", not (l -> r))$
][
```txt
  client <--(1)-- cart
  ^
  |
 (1)
  |
  |
  shop --- arbitrator --- tx
  ```
]

#pagebreak()

#slide[
  == Causal Dependencies
]

#pagebreak()

#slide[
  == References

  #bibliography("bibliography.yml", title: none, style: "ieee")
]
