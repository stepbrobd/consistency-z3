# What is "visible"

Some information here are outdated, please refer to the source code for the
latest definitions.

All below definitions have common constraint of all operations must be invoked
on the same object. The preconditions of concurrent operations include the same
object constraint anyways.

Definition of atomic operations: an operation is considered as atomic if the
logical start time equal to its logical end time.

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

- Can view: A non-deterministic pairwise partial ordering between a write
  operation (let's call it a) and a read operation (call it b) that solely
  depends on time stamps (conceptually, the read happens after or during the
  write).
  - non-concurrent (`a1`): `op.rtime(a) < op.stime(b)` (i.e. totally ordered)
  - concurrent (`a2`):
    `And(op.stime(a) >= op.stime(b), op.stime(a) <= op.rtime(b), op.rtime(a) >= op.stime(b), op.rtime(a) <= op.rtime(b))`
  - concurrent (`a3`):
    `And(op.stime(a) <= op.stime(b), op.stime(a) <= op.rtime(b), op.rtime(a) >= op.stime(b), op.rtime(a) <= op.rtime(b))`
  - concurrent (`a4`):
    `And(op.stime(a) >= op.stime(b), op.stime(a) <= op.rtime(b), op.rtime(a) >= op.stime(b), op.rtime(a) >= op.rtime(b))`
  - concurrent (`a5`):
    `And(op.stime(a) <= op.stime(b), op.stime(a) <= op.rtime(b), op.rtime(a) >= op.stime(b), op.rtime(a) >= op.rtime(b))`

- Viewed: A non-deterministic pairwise partial ordering between a write
  operation and a read operation that builds atop "can view". Aside from the
  timestamps fall into one of the "can view" cases, `ival` of the write must
  match the `oval` of the read. In case of a write happened after or concurrent
  to the aforementioned write, viewed relation enforces the output of the read
  to be either of writes (only one can be chosen). In visible/visibility
  definition, the transitivity of viewed relation is implicitly enforced.

- Visible = viewed + arbitration: A deterministic pairwise between any
  operation.
  - Case 1: read-read pair: previous read needs to track it's closest visible
    write, then propagate the closest visible write to the latest read
  - Case 2: read-write pair: undefined for now
  - Case 3: write-read pair: simply viewed (value equivalence) + arbitration
    (preserve the previously viewed ordering as if it's a linearized ordering in
    the first place)
  - Case 4: write-write pair: undefined for now
