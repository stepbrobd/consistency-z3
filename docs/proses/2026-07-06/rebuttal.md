**A-Q1 Bypassing SMT**

Although our current implementation does not support this, if one wants to
bypass pairwise checks, it could just be a table lookup (Table 1). However, this
will not work for composed models, e.g., EC+MR+MW and its strength cannot be
implied just from the model, and the same logic applies for checks on the edge
constraint path, as the context from previous iterations needs to be preserved.
Also, if the user is providing their own custom consistency semantic, SMT is
required.

**B-Q1 Concrete counterexamples**

We have a witness extraction test under tests/test\_witness.py, the tool can
generate SMT-LIB code and execute with Z3 or CVC5 to obtain models or unsat
cores.

As an example, EC (guarded under can-view) is not compatible with MR: the solver
can find a write operation a, read operations b and c, where so(b, c). The
witness sets vis(a, b) \= true, vis(a, c) \= false. EC is satisfiable under this
assignment (hb acyclicity, and event ordering trivially satisfies RVal under
can-view). MR fails as vis(a, b) /\\ so(b, c) \=\> vis(a, c) is required.
Verbatim, the anomaly is when a reader sees a write but the subsequent read in
the same session loses the previous successful read.

**B-Q2 System model assumptions and guarantees**

SemantiX assumes an asynchronous network model: messages may be arbitrarily
delayed, reordered, or dropped, and the network may partition, though not
permanently. Nodes may crash but are assumed to recover with their state intact
(i.e., dependent operations are remembered across failures; otherwise, user
sessions must terminate). Operations are modeled as atomic request-response
pairs in the sense that every operation sort must have all required fields
populated. However, non-atomic runtime behaviors such as cancellation or partial
execution can be represented by setting op.rtime to the interruption time and
placing a partial/invalid marker in op.oval. Concurrency is captured via
overlapping invocation-return intervals as formalized in Section 3.3. Object
scope is handled per-semantic: relations such as ob are scoped within each
consistency model's constraints, and when composing multiple semantics,
cross-object equivalences are expressed as static constraints on edges
(trivially asserted as equality in our current implementation, but extensible to
richer relational constraints).

While SemantiX checks should always be correct, if the actual system
implementation does not faithfully implement the target semantics, the SemantiX
results may mismatch with the implementation. Similarly, if users provide
ill-formed DMs or AppGraphs, SemantiX results may mismatch with the
implementation, but verifying the correctness of the DM/AppGraph encodings is
outside the scope of this work. See B-I for details.

**B-Q3 Modeling large scale applications with 20+ services**

Although the largest example we show involves 11 components, SemantiX is capable
of scaling to a larger-scale application through modular decomposition as
described in the scalability section. A big service system can be decomposed
into independently verifiable subgraphs, each checked, then re-composed.
Realistically, most nodes have fixed logic with a relatively small number of DB
nodes which may need DM search: searching 17^3 to 17^5 combinations can take
from minutes to days per Table 2\. Still, if users provide candidate DMs the
check can complete in subsecond. Also, see C-Q2 for encoding efforts.

**B-Q4 Why exclude liveness from EC and why combine definitions of CC**

We are focusing on safety, and liveness is outside of our current project’s
scope. Eventual convergence (liveness) requires reasoning over unbounded
execution, and it is considered hard if not impossible to express with finite
SMT formulas. Thus, we mainly focus on the safety components following the
safety/liveness separation as in many other works \[9, 48\].

For CC, our wording used around line 300 is confusing. We are not “combining”
preexisting definitions, we are mostly following writes-into semantics in causal
memory \[5\] but cross checked preexisting definitions. We will clarify this in
the revision.

**C-Q1 Automated encoding**

Full automation of AppGraph construction is not currently supported and this
could be an interesting future direction. The AppGraph topology generation may
be automated, but it is not straightforward to automate the entire process. For
the topology, for example, k8s service mesh, or api gateway specs can be derived
into an AppGraph but without the semantics.

**C-Q2 Encoding effort**

We expect 1-5 person hours per application once the specifications are well
defined (coding is relatively trivial compared with abstraction and
conceptualization of the underlying systems). For larger applications, we expect
linear effort proportional to the number of nodes and edges in the AppGraph.

**—Answers below address concerns embedded in the comments—**

**A-I Plan for new models**

We are planning on exploring and adding more semantics whose semantic strengths
lie between causal consistency and linearizability.

**A-II Kater**

We thank the reviewer for pointing out the related work that we missed in the
weak memory model domain. We will reflect this in the related work section in
our revision.

**A-III Visibility well formedness**

The definition is stratified by operation type: cases 3, 4 (write first) are
non-recursive base cases, and cases 1, 2 (read-first) reference visibility only
at write first position and dispatch to base cases in 1 step. Recursion depth
strictly decreases (1 for read, 0 for write) in every occurrence thus the
definition is bounded and well formed. Acyclicity and transitivity are separate
axioms on the resulting relation to enforce strict partial order. In
implementation, vis is a free theorem (uninterpreted function in SMT), and we
are imposing axioms (recursive definition \+ acyclicity \+ transitivity) on the
uninterpreted function so that the solver can find interpretations that satisfy
what we specified.

**B-I Soundness of the models**

The models are defined while faithfully following the widely adopted axiomatic
definitions with our new vis definition and Table 1 partly shows the correctness
of our model encoding. We have high confidence that our models are correct as
the known semantic definitions and the encoded models' definitions are in
similar formats; it is easy to compare the two.

**B/C-II Presentation**

We will clarify symbols at first use, state assumptions upfront, and move Fig. 5
closer to its reference.

## **ISTA 2026 Submission**

We thank the reviewers for insightful feedback. We first answer explicit
questions and address other reviewer concerns.

**A-Q1 Bypassing SMT**

If you want to bypass pairwise checks, it would just be a table lookup (Table
1). Though note that this will not work for composed models (e.g. EC+MR+MW and
its strength cannot be implied just from the model; the same logic applies for
checks on the edge constraint path, as the context from previous iterations
needs to be preserved). Or, if the user is providing their own custom
consistency semantic, SMT is required.

**B-Q1 Concrete counterexamples**

We have a witness extraction test under `tests/test_witness.py`, the tool can
generate SMT-LIB code and run with Z3 or CVC5 to obtain models or unsat cores.

Counter example, EC (guarded under can-view) is not compatible with MR: the
solver can find a write operation a, read operations b and c, where so(b, c).
The witness sets vis(a, b) \= true, vis(a, c) \= false. EC is satisfiable under
this assignment (hb acyclicity, and event ordering trivially satisfies RVal
under can-view). MR fails as vis(a, b) /\\ so(b, c) \=\> vis(a, c) is required.
Verbatim, the anomaly is when a reader sees a write but the subsequent read in
the same session loses the previous successful read.

**B-Q2 System model assumptions**

Operations are modeled as atomic request-response pairs (atomic in the sense
that the operation sort must have all fields present, but they can model
“non-automic operations” in runtime where if you want to express that an
operation is canceled or interrupted during execution, you can set the op.rtime
to the time where it stopped, and put value representing partial/invalid in
op.oval field). Concurrency is modeled as overlapping intervals (see visibility
definition in Section 3.3).\
Our tool is a high-level semantic checker, and it is implementation agnostic and
can be applied to different implementations and environments. Still, SemantiX
assume an asynchronous network (messages can be arbitrarily delayed, reordered,
and dropped, i.e., op.rtime becomes unbounded, marked by op.returned bool sort),
network can be partitioned, but not permanently, and nodes can crash but
eventually come back up with the states (e.g., remembering the dependent
operations).\
Object scopes are modeled per semantic (i.e. MR, RYW, if they require object
related relations, the objects are referenced only within their semantics’
scope). When composing/checking multiple semantics, the objects must have static
constraints (in our code, we trivially asserted equivalence), but more complex
object relations can be modeled with edge constraints.\
If a system violates the advertised model, our verdict is only as trustworthy as
the assumption.

**B-Q3 Modeling large scale applications with 20+ services**

Although the example we showed in the paper has limited scale, SemantiX is
capable of scaling to a larger-scale application through modular decomposition
as described in the scalability section. A big service system can be decomposed
into independently verifiable subgraphs, each checked, then re-composed.
Realistically, most nodes have fixed logic, maybe a few DB nodes need DM search
(17^3 to 17^5 combinations, competition time from minutes to days per Table 2).
If users provide candidate DMs search is unnecessary and the check can complete
in subsecond. Also, see C-Q2 for encoding efforts.

**B-Q4 Why are we excluding liveness from EC and why are we combining the
definitions for CC**

Eventual convergence (liveness) requires reasoning over unbounded execution, and
it's considered hard/impractical to express with finite SMT formulas (solvers
returning unknown or hang indefinitely). Thus we mainly focus on the safety
components following the standard safety/liveness separation \[9, 48\].\
For CC, our wording used around line 299 is confusing. We are not “combining”
preexisting definitions, we are mostly following writes-into semantics in causal
memory \[5\] but crossed checked preexisting definitions (we are asserting CC
with EC, 4 session guarantees and PRAM which implies the currently known partial
orderings provided by mainstream CC definitions). There is no prior agreed upon
standard definition for causal consistency (and there are many variants of
causal consistency models) across literature.

**C-Q1 Automated encoding**

In the sense of AppGraph topology, yes, but fully automated? No. For example k8s
service mesh, or api gateway specs can be derived into a AppGraph but without
the semantic constraints (we can use this to do fully automated search but
probably will not turn out to be useful because the execution time graphs
exponentially based on the \# of nodes, also edge constraints are not specified
making the spec underspecified). However as its 2026 one can utilize LLM tools
for some automation, refer to the automated reasoning papers (e.g. Terrance Tao
using Claude Code for theorem proving available on his YouTube channel).

**C-Q2 Encoding effort**

We expect 1-5 person hours once the specifications are well defined (the coding
is relatively trivial compared with abstraction and conceptualization of the
underlying systems).\
Our case studies code was constantly changing (also the specifications are
changing during meetings/discussions) during tool development so our time is a
lot longer.

**A-Q2 Kater**

We thank the reviewer for pointing out a related work that we missed in the weak
memory model domain. We will reflect this in the related work in our revision.

**A-Q3 Visibility well formedness**

The definition is stratified by operation type: cases 3, 4 (write first) are
non-recursive base cases, and cases 1, 2 (read-first) reference visibility only
at write first position and dispatch to base cases in one step. Recursion depth
strictly decreases (1 for read, 0 for write) in every occurrence thus it is
bounded (and well formed). Acyclicity and transitivity are separate axioms on
the resulting relation to enforce strict partial order. In implementation, vis
is a free theorem (uninterpreted function in SMT), and we are just imposing
axioms (recursive definition \+ acyclicity \+ transitivity) on the uninterpreted
function so that the solver can find interpretations that satisfy what we
specified.

**B-Q5, C-Q3 Presentation**

We will clarify symbols at first use, state assumptions upfront, and move Fig. 5
closer to its reference. We are cross-checking our encodings against independent
definitions in Rocq (previously Coq) in a separate ongoing effort.

**Review \#405A \- Overall merit \- 4\. Accept**

**Weaknesses**

\- Could one enumerate common models and bypass the SMT checks by simply
checking that the provider has a model stronger than the consumer's needs?

I’m not sure whether the reviewer is implying if the “bypass” is a weakness or
feature?\
I mean it surely can be bypassed and its literally just a table lookup (Table
1\)\
In the sense of “bypassing” to save SMT solver calls, it can only happen if we
are doing simple pairwise checks but not for composed models (e.g. EC+MR+MW and
its strength cannot be implied just from the model (same logic applies for
checks on EC path, as the context from previous iterations needs to be
preserved).\
Or, if the user is providing their own custom consistency semantic, SMT is
required.

\- Do we expect new consistency models to be developed regularly?

No? It’s a one shot academic project why would anyone try to use this lmao\
Plan to expand in between causal and linieriable (sequantial…)\
**Detailed comments for authors**

You may want to explore if recent work in the weak memory space using regular
expressions (Kater: Kokologiannakis et al.) would also be useful in this context
(I think so).

Do we need to respond to this?

A small comment: the visibility relation is recursively defined. You may want to
remark that the definition is well-formed.

It's well-founded because it has a bounded recursion depth of 1\. If we make
things clear:

1. a.type \= rd, b.type \= rd, x.type \= wr where vis(x, a) \=\> vis(x, b)
2. a.type \= rd, b.type \= wr, x.type \= wr where vis(x, a) \=\> vis(x, b)
3. a.type \= wr, b.type \= rd (base case)
4. a.type \= wr, b.type \= wr (base case)

In 1\. vis(x, a) goes to 3\. and vis(x, b) also goes to 3\.\
In 2\. vis(x, a) goes to 3\. and vis(x, b) goes to 4\.\
(I go more in depth on this and proof that the recursion is founded but since
the reviewer mentioned this is a “small comment” so we probably don’t need to do
so?)\
Overall the recursion is well-founded, and on top of the recursive definition,
we additionally impose acyclicity and transitivity on visibility (not in the
recursion) but they exist to enforce strict partial order. In implementation,
vis is a free theorem (uninterpreted function in SMT), and we are just imposing
axioms (recursive definition \+ acyclicity \+ transitivity) on the uninterpreted
function so that the solver can find interpretations that satisfy what we
specified.

**Review \#405B \- Overall merit \- 3\. Weak accept**

**Weaknesses**

\- Correctness evidence could be stronger. Table 1 validates relative ordering
between models but does not test whether individual encodings admit exactly the
right set of executions.

Sure, do you want us to go in depth and prove trivial stuff like for all our
definitions like vis above? There’s something call page limit bro, if you want
to see “correctness evidence” go review PLDI or CAV or smth like that

\- System model assumptions are implicit. It would help to state assumptions
(e.g., operation atomicity, fault model, single-object scope) upfront so readers
can assess applicability.

For operations, they are modeled as atomic request-response pairs. Atomic in the
sense that the Op must have all the fields present, and they can module
non-automic operations in the “normal sense” where if you want to express that
an operation is canceled, you can set the rtime to the time where it stopped,
and put value representing partial/invalid in oval field. Concurrency is modeled
as overlapping intervals (see vis definition illustration).\
Our tool is a high-level semantic checker, and is implementation agnostic and
can be applied to different implementations and environments. Our basic
assumption is that the network is asynchronous—messages can be arbitrarily
delayed, reordered, and dropped (i.e., op.rtime becomes unbounded, marked by
op.returned bool sort), and network can be partitioned, but not permanently—,
and nodes can crash but eventually come back up with the states (e.g.,
remembering the dependent operations) when it crashed.\
This tool checks safety properties assuming liveness (eventual visibility as
baseline). NO crash failure, NO network partition or msg losses etc (remove).
This is specifically made for checking the safety properties for consistency
specs, not implementations. The aforementioned scenarios are considered to be
implementation specific hence out of scope, not the compatibility layer we are
aiming for.\
I assume the “single object” scope here meaning the object in same-object
pairwise relation? If so, the object scopes are modeled per semantic (i.e. MR,
RYW, if they require object related relations, the objects are referenced only
within their semantics’ scope). When composing/checking multiple semantics, the
objects must have static constraints (in our code, we trivially asserted
equivalence), but more complex object relations can be modeled with edge
constraints.

\- Case studies are small-scale. A larger case study would better support the
paper's framing as a practical framework.

~~See scalability section.~~ We handle large scale applications by semantically
decomposing them into digestible chunks and checking them separately (see the
shopping mall case study and how the nodes are aggregated, and how the cross
causal chain based composition). Also for large applications, without dissecting
them, the search space would be too large as demonstrated.

**Detailed comments for authors**

\*\*Soundness.P\*\* The paper's value depends on users trusting that a passing
check means their configuration is actually compatible. Table 1 confirms
pairwise results match known theory, but this is a necessary condition, not a
sufficient one. For instance, one thing I would like to see is the
counterexample executions the solver produces for the incompatible cells in
Table 1, with a walkthrough of a representative sample showing the witness
genuinely violates the target model. This would help readers assess whether the
solver is producing real violations or artifacts of the encoding.\
Use counter examples like EC vs MR for visibility on read propagation, also add
some traces and math notations\
\*\*Importance.\*\* As a first work in this direction, the small scale of the
case studies (at most 11 components) is understandable. That said, a moderately
larger case study (e.g., 20+ services) would go a long way toward demonstrating
that AppGraph construction and SMT solving remain practical beyond the current
examples.

\*\*Verifiability and Transparency.\*\* The authors state code and data will be
available upon acceptance. However, the paper's formal presentation has gaps
that hinder understanding: several symbols are introduced without clear
definition or become difficult to track across sections, and the system model is
left entirely implicit. For a paper centered on formal reasoning, the exposition
should be tighter.

\*\*Presentation.\*\* Generally readable, but the formalization could be
clearer. Symbol definitions are sometimes missing or separated far from their
usage. For instance:

F and ctx appear in the EC definition without prior introduction\
F is introduced as contextual return value consistency (mentioned in the
eventual consistency survey with the same definition?)\
H is used throughout Section 3.1 before being explicitly defined as a history;\
TODO\
acyclic(hb) is never given a type signature or formal meaning;\
The foo(bar) style is the same as the rest of the paper. acyclic(hb) means
specifically the happens-before relation forms a DAG i.e. no cyclic casual
dependency\
and the motivation for excluding liveness from EC and combining multiple prior
definitions for CC is not clearly explained.\
Mostly because of eventual convergence is not specifiable in SMT clause
(infinite traces?) what was the actual reason for this?

**Questions for authors' response**

1\. Can you provide concrete counterexample executions (witnesses) for a few
incompatible pairs in Table 1, and walk through why each witness genuinely
violates the target consistency model?

This is probably the hardest one to answer… I think we already have a violation
example for shopping mall, I’ll look thru that and add a pairwise counter
example.

2\. What are the explicit system model assumptions underlying your formalization
(e.g., fault model, operation atomicity, single-object scope)? Under what
conditions would SemantiX's guarantees not hold?

See above

3\. Have you considered applying SemantiX to a larger-scale application (20+
services)? If so, what were the main challenges in AppGraph construction and
solver tractability?

See above

4\. Several design choices in the formalization are not motivated: why exclude
liveness from EC, and why combine three separate prior definitions for CC rather
than adopting one? Could you briefly justify these decisions?

Partially answered above\
(mention liveness is not well defined for other semantics other than EC)

**Review \#405C \- Overall merit \- 4\. Accept**

**Weaknesses**

\- Limited experimental results

**Detailed comments for authors**

On the weak side, the experimental results are limited. In particular, the
system has been applied only to three case studies. This shows a limitation in
the approach, since it requires manual encoding of the semantics of the systems
under analysis. Therefore, it requires significant manual effort and does not
scale up. The authors did not discuss if and how such an approach might be
automated or at least made more scalable. However, I expect this would be rather
complex and challenging, due to the variety of technologies used in distributed
systems and the fact that formal semantics is often hard to precisely derive
from an application's code.

As a minor side note, Figure 5 appears 6 pages after it was introduced with a
very long caption (as many others). I'd suggest moving the detailed descriptions
of the figures into the text and anticipating Figure 5\.

**Questions for authors' response**

1\) Could the encoding of an application in AppGraph be automated? How?\
In the sense of topology, yes, but fully automated? No. For example k8s service
mesh, or api gateway specs can be derived into a appgraph but without the
semantic constraints (we can use this to do fully automated search but probably
will not turn out to be useful because the execution time graphs exponentially
based on the \# of nodes, also edge constraints are not specified making the
spec underspecified). However as its 2026 one can utilize LLM tools for some
automation, refer to the automated reasoning papers (e.g. Terrance Tao using
claude code to prove stuff)\
2\) How much time did it take to perform the manual encoding of the three case
studies in AppGuard?\
Damn a lot of time is put into these case studies during development idk\
But based on estimation i would say thinking thru the correct model and
abstraction is harder than the actual coding so if you have a concrete plan the
implementation might take a few hours.\
Mention my estimation but also add if all constraints are predefined the coding
part is trivial and can be done within hours
