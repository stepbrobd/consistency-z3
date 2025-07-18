# Meeting notes

Hydra Evaluation and Binary Cache:

- Jobset: <https://hydra.ysun.co/jobset/stepbrobd/consistency-z3>
- Cache: <https://cache.ysun.co/public>
- Key: `public:Y9EARSt+KLUY1JrY4X8XWmzs6uD+Zh2hRqN9eCUg55U=`

## 2025-07-18

- media example, no need for stripping out the graph, finish client review flow
  formalization
- section 4, composition check and compatibility check revisit

- color cart, shop, tx log green, also change arbitrator node name to API node
  or some sort
- when the checker finds the first correct combination (excluding shopping mall)
- fix shop:
  - for the shopping mall example write it as if arbitrator requires RYW from
    shop and client need MR
  - rerun test and timing
- add pairwise timing to table in eval section
- figures (shop, media, xc)
- remove needs from the media figure but leave provs on db nodes

## 2025-07-17

- in case study media example
  - formalize in writing chain of dependencies:
    - user must register before login
    - user must be logged in to write reviews
    - to write reviews, review api must check movie metadata exist
  - strip out portion of figure 4 to show dependent ops and ec
- in shopping mall example, make graph shorter
- redraw figure 4 and xc graph (make it look like a binary tree)

## 2025-07-16

- implement timing for media example (with sorted ordering), only need to plugin
  to slots where `provs` is not None
- timing info for pairwise checks (same table 1 but instead of T/F put the
  timing numbers in there)
- for xc timing, claim that the weakest cases can already be found, and we have
  these cases of failures/timeouts, we could've stopped the check (and things
  like this)
- write about machine specs for benchmark
- make a dedicated evaluation section add numbers and specs
- [off loaded] in case study writing, hide details (like a quiz to reviewers)

## 2025-07-14

- timing (limit each check to 10sec and terminate use a special marker)
- `/tmp/tmpw5a4uzix/xc_timing_results.csv` on framework laptop
- sort the `product()` call and start from the combo with the smallest score
- output should be a table
- time of min time to find the combination with the smallest score
- when user plug in the correct combo, the time to check the correctness
- leave timing media example as future work (17^9)

## 2025-07-12

for timing

- time each pairwise check (not the app level graph checking table 1)
- for graph check, 1. give correct combination 2. let the checker pick
- for media example, leave data dependency as is and just generate slots for the
  semantics
- write a generation function that checks all semantics and all combinitions of
  the semantics
- assign score to each of the semantic, and generate permutation for all
  semantics, sort by sum from low to high and plug in one by one
- eventual -> 0, session -> 1, PRAM -> 3, causal -> 4, linearizablity -> 5
- selling point: checker can find the weakest combinition

## 2025-07-02

- [high prio] lift PRAM write-write arbitration to visibility
- find out who starred my repo and add that SAT solver work to related work
  (follow up on slack)
  - https://hengxin.github.io
  - https://github.com/hengxin/smt-transactional-consistency-artifact
  - write a summary and add to related work
- eval: when timing the checks, save timing info per combination and num of
  checks
- continue writing and graphs
- [offloaded] rewrite intro and mentions of DAG
- [offloaded] request to proofread and modify background and motivation section

```
- intro
- background and motivation (consistency semantics, how ppl design micro svcs, potential bugs)
- overview (less technical high level overview <components, what it does, how the operation is serialized, binary relation, ...)
- design (defs of visibility + short version of consistency semantics section, with individual semantic modeling with pairwise checks)
- composition (use one simplified movie example, use app design to explane <like conditional update, dependent ops, how to use nodes/edges>, nodes/edges, provs/needs)
- case study (shop <simple>, movie <simple>, xc <in details>)
- eval (timing (see above), num of compatible assignments for some example)
- related work (domain specific solver, memory model, starred repo (see above), add more)
- conclusion
```

## 2025-06-17

- lift PRAM write-write arbitration to visibility - skipped
- add safety prperties of eventual (non-transactional pp. 10, no circular +
  rval) - done
- add failure (counter) example to motivation section (use as problem
  statement) - done
  - give simple example of practical app
  - plugin one semantic and it passes the check
  - switch to a failing semantic
- go through introduction - done
- new table for each case study on semantics:
  ```
  | node name | needs | provs | edge constraints | edge destination |
  ```
- graphs for visibility

## 2025-06-05

- how to present the problem?
  - translated to smt clauses? the challenges arent enough, thus focus more on
    the theory side
  - can focus more on the theoretical side, i.e. how to model the consistency
    models, and how to compose them
- fix: PRAM uses a rougue arbitration (maybe trying finding the paper with
  arbitration in PRAM)
  - for vis define read-write pair and write-write pair (propagation of writes
    across processes)
  - come up with example and plot
- timing diagram for visibility

## 2025-05-19

- fix linearizablity using single order definition on nontransactional pp.8
  principal of eventual consistency pp.59
- failure examples
  - simple app constraint, dont satisfy at first level
  - failure at second level (e.g. in media, client to API layer can succeed but
    API to db level fails)
- motivating examples/cases add to background and motivations
- use a running example for design principal (maybe arbitrator?)
- better figures
- add MixT and Noctoa to related work

## 2025-05-15

- [hi prio] dump movie/shopping with graphs in text (in
  modeling-real-world-applications.tex)
- add causal to table
- use a running example for design principal
- prose for failure senario
- [low prio] add eventual consistency that does not have any constrtaits
  - add failure example against
  - replace storage semantics
  - replace edge constraints (for failure simulation)
- [low prio] add MixT to related work

```
- intro
- background and motivation (consistency semantics, how ppl design micro svcs, potential bugs)
- overview (less technical high level overview <components, what it does, how the operation is serialized, binary relation, ...)
- design (short version of consistency semantics section, with individual semantic modeling with pairwise checks)
- composition (use very simple examples <like dependent ops, how to use nodes/edges>, nodes/edges, provs/needs)
- case study (shop <simple>, movie <simple>, xc <in details>)
- eval (timing, difficulty of modeling, failure cases, ...)
- related work
- conclusion
```

## 2025-05-12

- a list of relevant papers
- failure/counter examples
- pull standalone lit review as related work (docs/proses/2025-01-06)
- change can-view to graph

## 2025-05-07

- making the application examples (shopping, movie, xc) to be more concrete, as
  in:
  - each node/edge, what needs/provs mean (in table, see the whiteboard)
  - explain the differences between using different set of symbols vs. using
    different instantiation of operations
    - movie example - divide by operations (different instantiation), similar to
      XCY
    - XC example - divide by symbols (as in each symbol is different objects in
      storage system)
- come up with a "principle" of how to model applications (when and why using
  symbol, differnet symbol, vs diferent instantiation of operations)

## 2025-04-18

- explain cross causal in writing (due Apr. 26)
- from the inline docs, mr, mw, ... on the rhs are "pseudo nodes" (directly
  added to svc*'s prov)
- at first level check, upper level's svc node need field will be empty, need
  will be causal
- after aggregation, svc's prov will be pseudo node' semantic + result of
  aggregation from lower layers
- symbol equivalence added to edges

## 2025-03-28

- parameterize all models' symbol usage
- for tests other than cross causal, set the models to use the same set of
  symbols
- check the composition of 3 causals

## 2025-03-21

- put XCY consistency on hold
- impl 4 session semantics with causal cross storage

## 2025-03-14

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

## 2025-03-04

- just the shim layer for weak consistency + happen-before
- review lineage definition
- XCY definition currently uses hb instead of xcy (fix needed)
- low priority:
  - https://dl.acm.org/doi/10.1145/1345169.1345178
  - https://dl.acm.org/doi/10.1007/s00165-014-0303-1
  - https://link.springer.com/chapter/10.1007/978-3-319-67531-2_17
  - https://team.inria.fr/veridis/publications/

## 2025-02-20

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

## 2025-01-31

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

## 2025-01-23

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

## 2025-01-17

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
