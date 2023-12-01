#import "@preview/polylux:0.3.1": *
#import themes.simple: *

#let title = "Initial Exploration"
#let author = "Yifei Sun"
#let date = datetime(year: 2023, month: 12, day: 5)

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
  == Objectives

  + model distributed semantics
  + verify said semantic satisfies its specifications
  + check pair-wise compatibility
  + composition of two or more systems
]

#slide[
  == Definitions: Operation

  Operation are tuples: $("proc", "type", "obj", "ival", "oval", "stime", "rtime")$ @viotti2016consistency[pp.3].

  ```py
  class Operation(NamedTuple):
      proc: int # process id
      type: str # operation type
      obj: int # object id
      ival: Any # input value
      stime: int # start time
      rtime: int = None # return time
      oval: Any = None # output value
      symbol: str = None # readable representation
  ```
]

#slide[
  == Definitions: History

  A set of operations, contains all operations invoked in a given execution,
  describes the *observable outcomes of executions* @viotti2016consistency[pp.4].

  It's possible that a set of symbols and their relations:
  - does not form a history (invalid)
  - forms multiple histories (ambiguous)

  Types:
  - $"H"|_"rd" = {"op" in "H": "op.type" = "rd"}$
  - $"H"|_"wr" = {"op" in "H": "op.type" = "wr"}$
  // there are more types
]

#slide[
  == Definitions: History

  Relations:
  - returns-before: $"rb" eq.delta {("a","b"): "a","b" in "H" and "a.rtime" < "b.stime"}$
  - same-session: $"ss" eq.delta {("a","b"): "a","b" in "H" and "a.proc" = "b.proc"}$
  - session-order: $"so" eq.delta "rb" sect "ss"$
  // there are more relations

  ```py
  class History:
      def __init__(self: Self,
        ops: set[Operation],
        **kwargs: set[Relation]
      ) -> None: ...
  ```
]

#slide[
  == Definitions: Anstract Execution
  An abstract execution is
  - built on top of a history
  - *captures the non-determinism, and constraints*
  - an event graph $"A" = ("H", "vis", "ar", "hb")$ @burckhardt2014principles[pp.25-27,34-35]
]

#slide[
  == Definitions: Anstract Execution
  Relations:
  - $"vis"$ (visibility): $a arrow.r.long^"vis" b$
  - $"ar"$ (arbitration):
  - $"hb"$ (happens-before):
  // there are more relations

  ```py
  class AbstractExecution:
      def __init__(self: Self,
        hist: History,
        **kwargs: set[Relation]
      ) -> None: ...
  ```
]

#slide[
  == References

  #bibliography("bibliography.yml", title: none, style: "ieee")
]
