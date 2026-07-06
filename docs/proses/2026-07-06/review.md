# ICSE 2026, Research Track Paper #998 Reviews and Comments

Paper #998 SemantiX: A Compatibility Checker between Applications and
Compositions of Distributed Systems

# Review #998A

## Overall merit

3. Weak accept

## Paper summary

The paper presents the SemantiX framework for checking the semantic
compatibility between applications and the composition of distributed services
with heterogeneous consistency models. SemantiX provides in-built distributed
system modules to represent distributed storage services using commonly used
consistency models, including eventual consistency, linearizability, session
guarantees, PRAM, and causal consistency. It introduces abstractions for
encoding the constraints of applications with an acyclic graph structure that
represents constraints between components, and checks whether these constraints
are satisfied against a combination of distributed system modules using an
SMT-based approach. The paper demonstrates that SemantiX can handle complex
system compositions through three case studies: a movie streaming service, an
e-commerce service, and a cross-service causal distributed storage service.

## Strengths

- Novel framework for a highly relevant problem for today’s heterogeneous
  systems
- Rigorous approach to formally checking the compatibility of application and
  consistency constraints
- The application logic of the case studies and how SemantiX handles them are
  explained in detail

## Weaknesses

- Source code for the framework or applications is not available
- Unclear scalability to real-world, large-scale applications
- The use of the system from the user's point of view could be explained better

## Detailed comments for authors

Novelty:

The paper provides a novel approach for checking the compatibility of
application logic with the consistency semantics of distributed modules used,
specifically in compositional settings that utilize diverse consistency models.

Relevance:

The studied problem is highly relevant to today’s software systems, which often
comprise multiple components with different consistency constraints.

Rigor:

SemantiX offers a rigorous approach to checking compatibility by reusing
well-established consistency definitions, introducing new definitions to clarify
existing vaguely defined visibility concepts, and presenting a method for
formally checking compatibility.

The framework provides abstractions to model applications and express their
constraints. While the paper focuses on explaining the workings of the
framework, it would be helpful to expand on how users utilize the framework
(e.g., what inputs they provide) to model their constraints.

The evaluation shows that SemantiX can verify consistency guarantees for the
presented case studies in a reasonable amount of time. However, the scalability
to large-scale systems is unclear, given the relatively small lines of code to
encode the studied benchmarks.

Verifiability & transparency:

The source code and evaluation data for SemantiX or the case study applications
are not available.

Presentation:

In general, the paper's presentation is clean and easy to read, despite being
heavy on abstract definitions and concepts. However, it could be beneficial to
review the formalizations. Some of my questions and comments are below:

- The viewed relation (line 528) requires (x,b) /in can-view, where both x, b
  \in H_{wr}. Is "can-view" not defined as a relation between a read and a write
  operation (as given in line 507)?
- Figure 3 could benefit from a more detailed explanation. For example,
  including sample read and written values along with the specific values of the
  "can-view" and "viewed" relations would be helpful. While the paragraph
  starting on line 540 provides some examples, additional details could be
  helpful, especially since the formalization of visibility is one of the
  contributions of the work.
- The formalization of the contextual return value policy (lines 403 and the
  formula on line 423) could be elaborated on for better understanding.
- You could consider introducing/referring to an example AppGraph while
  explaining the compatibility checking in Section 4.2 to make the explanation
  easier to follow.

Minor:\
Line 574: Typo in “strainghtforward”\
Line 647: “and” could use a different font.

## Questions for authors’ response

Q1: What inputs does the user exactly provide to the framework to model their
application constraints?\
Q2: What is the scalability of the method to large-scale programs?\
Q3: Are the source code and evaluation data for SemantiX available?

# Review #998B

- Updated: Oct 8, 2025

## Overall merit

2. Weak reject

## Paper summary

The paper presents a framework for automated checks of semantic compatibility
and composability of distributed systems. The main idea is to encode, in
predicate logic, the distributed consistency semantics (eventual consistency,
read-your-writes, etc.) that each node in the distributed system provides and/or
expects, and perform compatibility and composability checks via invoking an SMT
solver. The framework’s usefulness lies in early detection of incompatible
components/services. It can also be used for finding compatible data backends.
The framework is implemented in Python and its feasibility is evaluated using 3
example systems, specified and checked by the authors.

## Strengths

- Interesting and intuitive formalization, well presented
- Relatively novel approach
- Detailed supplementary material

## Weaknesses

- Problem formulation can be improved
- Missing information regarding the use of the framework by developers
- Questionable relevance/impact (related to the above)
- Evaluation targeting initial feasibility only, not usability from actual
  stakeholders
- Presentation can be improved (grammar, figures)

## Detailed comments for authors

#### Novelty

The novelty of the proposed approach lies in the automated verification, via SMT
solving, of distributed consistency constraints in an distributed setup, i.e it
focuses on the composition problem where different services can have different
distributed consistency semantics. The approach builds on and expands prior work
on formal definition of distributed consistency semantics. Overall, I found the
contribution original and its comparison to the state of the art convincing.

#### Rigor

The tackled problem is described in the introduction as “the mismatch of the
chosen system’s semantics and the application’s expected semantics could
introduce subtle and silent semantic bugs” but not exemplified/motivated enough
later.

The formal treatment of the subject, both in the background presented in Section
2 and the presentation of the distributed consistency models in Section 3, is
one of the strong aspects of the paper. I was able to get the important ideas
behind the formalization and found novel definition of visibility quite
interesting and well thought. I believe that Section 3 could have been even
better if the motivating example of Sec. 2.2 was used as a running example to
illustrate the semantics.

One specific question I had regarding the formalization is what is the “custom”
type of operation, and why it is needed.

When it comes to the description of the framework, I was missing important
information about the input (and the its form) expected from the developer. In
the end, after looking also at the code provided as supplementary material, I
realised that the end-user (developer) needs to provide a description of the
constraints propagated through the DAG of the system; this could have been
illustrated better in Sections 4 and 5.

When it comes to the evaluation, this takes the form of extracting some results
from three example systems specified by the authors. Although interesting to
read, I’m a bit doubtful about this type of evaluation since, although it
assesses the feasibility of the framework, it does not speak to its usability by
its targeted stakeholder, i.e. developers (see my comments on Relevance as
well).

Apart from the above point, the evaluation is rather unstructured since there
are no guiding research questions. Finally, in terms of methodology, the authors
use the term case study but these are example cases, not "case studies" in the
empirical sense.

#### Relevance

I found this aspect to be a shortcoming of the submission, since the paper does
not really provide any concrete idea on how the framework can be used in a
realistic setting.

First, if the target stakeholders are indeed developers, is it realistic to
expect that developers are familiar with axiomatic semantics and SMT encodings
(as mentioned in the beginning of Section 5? I very doubtful about that.

Second, how exactly the framework will be used by the developers and architects
is not really elaborated. What would be the phases in the development lifecycle
where the approach is most useful, what would be the inputs provided by the end
users and what the outputs to be expected from the system?

Third, what is the estimated extra effort needed to use the framework, and does
this pay off?

I found very hard to judge the relevance without even an initial
assessment/estimation of the above.

#### Verifiability and transparency

The paper provides enough details to understand the formal semantics and the
overall working of the framework, but lacks details when it comes to its use.
Some more information about this is provided in the detailed README of the code
repository provided as supplementary material, along with all the code. Overall,
I found the work verifiable.

#### Presentation

The paper is well structured but has some shortcomings in presentation when it
comes to the figures and to some grammar mistakes (harming readability at
places):

- Figures 4, 5, 6 should have been more consistent with each other: they
  describe the AppGraph for the different systems, having different details on
  the figures makes it confusing to the reader
- Line 89: “the number of proofs that need to be written could be several times
  longer in lines of code comparing with the implementation”
- Line 111: “Custom models defined in our interface are automatically
  compatibility with existing ones, and can be used to check its own
  satisfiability”
- Line 266: “to minimize anomalous users may experience.”
- Line 269: “The collection of constraints must be satisfied by what the
  consistency model of which metadata DB developer chooses provides.”
- Line 391: “where H_wr and H_rd are histories of reads and writes,
  respectively” -> this is the other way round, right?
- Line 655: “This checks if the chosen path provides guarantee of the
  destination (check_provs) is implied by the conjunction”

### Reaction to rebuttal

On my 3 questions/points of critisism:

1. How can the framework be used? The answer provided does not really add more
   information to what is in the paper, but at least it verifies my
   understanding that the users need to manually create an AppGraph instance
   using the provided Python library. I would have expected/preferred an answer
   that goes more into details on when the AppGraphs are created, when are they
   modified, when is analysis triggered, and how exactly is responsible for them
   (lead developer, architect?) That would provide me with a better
   understanding of the SE context assumed. I have to say that all the above can
   be somewhat deduced from the paper; I still think that it would be good to
   make the answers to the above more explicit.
2. What is the benefit for software engineers and how it can be assessed. Here,
   some ideas/options are provided on the what part, but not on the assessment
   part. I find the answer reasonable, however it also highlights that the
   benefit of the approach is not really shown in the current submission at
   least.
3. What is the cost/overhead for software engineers and how it can be assessed.
   Here again, the reply emphasizes lines of code, but I believe the real cost
   is on the learning curve to understand the notation and use it. To this, the
   answer of the authors is that they anyway expect people with formal
   background to use it.

Then, on top of my concerns which are only partially addressed as I analyse
above, there is the concern raised by Reviewer 3 on verifiability.

Given the above, I am increasing my score to weak reject, acknowledging the
well-argued answers but also the (for me) questionable usability and therefore
related potential impact of the approach at this stage.

## Questions for authors’ response

1. How can the framework be used in a realistic setting?
2. What is (an estimation of) the benefit of using the framework for a
   development team, how can this be assessed?
3. What is (an estimation of) the cost, in terms of extra effort, of using the
   framework for a development team, and how can this be assessed?

# Review #998C

## Overall merit

3. Weak accept

## Paper summary

The authors present SemantiX, a consistency compatibility checker for
distributed systems with subcomponents of heterogenous consistency. Their
SMT-solver based approach offers a principled way to check the validity of
existing consistency configurations as well as discover new ones.

Using existing consistency semantics from the literature (EC, MR, RYW, MW, WFR,
PRAM, CC, LIN), the authors build a formal framework for the compatibility
checker. Notably, the authors discuss and take advantage of the relationships
between consistency semantics. For example, stronger semantics can always be
used in place of weaker semantics, but this generally comes at the cost of
performance.

The paper introduces the AppGraph which mechanizes the compatibility checks
using a graph traversal that keeps track of node semantics. The idea is
well-motivated by multiple case studies with in-depth analysis and subsequently
a performance analysis in the evaluation.

## Strengths

- Very intriguing idea and well written + structured paper
- Extensive case studies that highlight motivation and evaluation
- Elegant solution rooted in graph-theory that tackles a relevant problem and
  takes advantage of the relationship between consistency semantics

## Weaknesses

- Some definitions are improper, especially one highlighted as a key
  contribution
- There are some difficult to parse paragraphs that would benefit from
  rephrasing

## Detailed comments for authors

**Novelty**

**Rigor**

The majority of definitions are sound. However, a major contribution of the
paper - the formal definition of visibility - is at least partially improper.
While the general intent is communicated well, the definitions of the $viewed$
and $vis$ relations have evident flaws as detailed in the verifiability section.

**Relevance**

An approach such as the one presented in this paper can be readily used in a
wide range of distributed systems contexts. The consistency compatibility
checker has support for a wide range of commonly used consistency semantics.

**Verifiability**

The authors claim a key contribution in their formal definition of visibility.
While the approach they use to achieve this goal is very promising, the formal
definition itself is unfortunately improper for the reasons listed below.

- L528 In the case
  $\exists x \in H_{wr} : (x, b) \in can\text{-}view \land a.oval = x.ival$, I
  believe there should be an additional constraint $(a,x) \in can\text{-}view$.
  Value equivalence does not mean the value originated from that specific write.
  The current constraint only compares the values, but it possible that there
  are multiple writes with the same value, of which only one is in a can-view
  relation with a.
- L558 I had a difficult time understanding this definition and the following
  description. It uses an awkward mix of set builder notation and recursive
  definitions that I am not sure is correct.
  - For example, the first disjunct contains the implication
    $(x,a) \in vis \Rightarrow (x,b) \in vis$ which is vacuously true for any
    $a$ that has an unrelated $x$. The expression can be rewritten as
    $\neg((x,a) \in vis) \lor (x,b) \in vis$ and is thus true for any
    $a \in H_{rd}, b \in H_{rd} : \exists x \in H_{wr} : (x,a) \not\in vis$ i.e.
    any pair of operations $(a, b)$ so that there is at least one operation x
    with which the a is not in relation.
  - The second disjunct has a similar issue
  - The third disjunct seems to be incorrectly formed as $a$ and $b$ are not
    used in the body of the quantifier

Otherwise, the authors present a generally complete picture of their approach
which is transparent and verifiable.

**Presentation**

- The can-view relation could be simplified. Perhaps it makes sense to
  additionally provide a logically reduced definition, that also takes advantage
  of the invariant $rtime \ge stime$?
- It may be more comfortable for the reader if the order of the arrow relation
  is swapped so that intuitively, events preceding their related object are left
  of the arrow pointing right
- L565 Unfortunately this paragraph was very difficult to understand

**Minor Comments**

- L152 (paragraph) Keep tense consistent instead of switching between past and
  present
- L234 This diagram is too crowded, it is difficult to see the arrows
- L300 Awkward wording - "whether" does not fit in this context
- L328 Awkward wording, perhaps rather "An operation can be conceptualized as an
  atomic action with a request-response pair..."?
- L407 For completeness sake, the arrow relation syntax should be explicitly
  introduced
- L407 The monotonic reads definition is the same as the monotonic writes
  definition
- L565 The next two paragraphs should use the same identifiers in the
  explanation as in the preceding $vis$ definition for clarity
- L574 Typo "straignforward"
- L582 Typo "is" -> "are"
- L694 Type "assume" -> "assumes"
- L793 Inconsistent notation compared to previous definitions.
  $ob(op_{login}, op_{rent})$ -> $(op_{login}, op_{rent}) \in ob$

## Artifact assessment

3. Satisfactory, i.e., the artifacts are in line with what is declared in the
   submission form or the paper [OR] the authors explained why the artifacts are
   not provided and I find the explanation to be reasonable.

## Cycle-2-Rebuttal Response by Author [Yifei Sun <ysun@hey.com>] (1299 words)

#### [A-Q1, B-Q1] What inputs does the user need to provide to the framework and how can the framework be used?

For application constraint checking, users can provide AppGraph(s) with:

- predefined constraints i.e. built-in DMs (available in code)
- custom DMs (conforming to operation and relation interfaces, and inherit from
  the base model) on the nodes/edges. If multiple DMs are given to node/edges,
  our framework can perform exhaustive search on all possible combinations.

Users also have the option to discharge AppGraph to `check` function with a
valid path assigned to `witness` argument to generate proof goals (example
available in `tests/test_witness.py`) and then further use external tools for
SMT solving.

Once the users learned the semantic requirements, writing AppGraph will not be
too challenging (see B-Q3 for efforts).

#### [A-Q2, B-Q1] What is the scalability of the method to large-scale programs?

AppGraph nodes and edges can be modularly composed for scalability. Large-scale
complex systems can be modularly broken down, reasoned among relevant modules,
and then composed into a monolithic node that exhibits the properties of
individual elements consisting of the composed nodes. An example usage of this
concept is demonstrated in the source tarball under `tests/test_aggregate.py`
based on Case Study 2 in Section 5.2. In the example, we split the AppGraph (see
Figure 5) into two parts: (1) Checkout, Tx Log, and Shop becomes an aggregated
entity (both entry/exit constraint flow from Checkout) after verifying the
composability providing logically equivalent constraints, and (2) the rest of
the graph, including a cross edge to Shop. With the modular design pattern in
mind, users of our framework can build sub-AppGraphs and verify them piece by
piece and then later compose them together into a service mesh, completing the
modeling of a large-scale application. Such modularity also allows the SMT
solving tasks for sub-components to be parallelized and the solved results to be
reused.

#### [A-Q3] Are the source code and evaluation data available?

They are submitted as Supplementary Material in HotCRP.

#### [B-Q2] What is the benefit of using the framework for a development team, how can this be assessed?

The primary benefits are: (1) early bug detection: identifying semantic
incompatibilities before they become runtime bugs, (2) architecture validation:
verifying system designs before implementation to prevent costly redesigns, (3)
pre-verification screening: quickly checking compatibility before investing in
formal verification efforts.

To elaborate more on the third point, formal verifications will take
significantly longer time and effort. It is uncertain if the proof will go
through depending on the concrete implementation. It is possible that developers
handling verifications will observe mismatch in proof specs v.s. implementation
at the last minute either due to incorrect proofs or implementations. Our tool
aims to be a quick checker to ensure compatibility holds before starting formal
proofs.

Our tool targets teams building critical distributed systems where correctness
justifies additional upfront modeling effort, particularly those already
considering formal verification approaches.

#### [B-Q3] What is the extra cost of using the framework for a development team, and how can this be assessed?

An increasing number of industry users are investing into formal verifications
either through interactive theorem provers or automated theorem solving. Our
tool lies in the automated solver category, aiming to be a high-level, low
learning curve, and low maintenance effort checker framework for use cases where
line-by-line formally verifiable specs (or just the critical sections) are too
costly. Our case studies required only 183, 80, and 252 lines of constraint
specification code respectively, significantly less than full formal
verification approaches. The framework provides automated SMT solving with
sub-second verification times, making it suitable for continuous integration and
delivery. Maintenance effort is minimal as constraints only change when service
interfaces or consistency requirements change, not with every code modification.

#### [Reviewer C] I had a difficult time understanding this definition and the following description (L558).

We acknowledge that our presentation could be better, but we believe the
recursive definition is sound. Please see our extended clarifications in
sections beyond 750 words.

#### [Reviewers A, C] Definitions of $\text{viewed}$ and $\text{vis}$ relations have flaws. In the viewed relation (L528): (A) is $\text{can-view}$ not defined as a relation between a read and a write operation? (C) additional constraint needed, and value equivalence does not mean the value originated from that specific write.

This is a typo and we will address this in the revision:
$(x,b) \in \text{can-view}$ should be $(a,x) \in \text{can-view}$. Also, note
that same-object constraint is implicitly enforced through $\text{can-view}$
relation, thus concurrent writes won’t cause any issue here.

### Answers to other points in the review:

#### [Reviewer C] The first disjunct contains the implication $(x,a) \in vis \Rightarrow (x,b) \in vis$ is vacuously true for any $a$ that has an unrelated $x$. The second disjunct has a similar issue.

Regarding vacuous truth claims, the reviewer treats our implications as
standalone logical statements, but they are constraints within an inductive set
comprehension. In the recursive definition, the cases for read-read pair and
read-write pair (along with the other two cases) are constraints within a set
comprehension that defines visibility relation inductively. The constraints only
apply when the existential quantification (and other conditions) in the
definition are satisfied. As for the interpretation of
$(x,a) \in vis \Rightarrow (x,b) \in vis$, we want to convey the transitivity of
visibility (same goes for the second disjunction).

#### [Reviewer C] The third disjunct seems to be incorrectly formed as $a$ and $b$ are not used in the body of the quantifier.

In this case, it appears that there’s a slight misunderstanding of the notations
we are using. We admit we overly simplified the notations, but $a$ and $b$ are
the parameters being defined in the relation (i.e. $a$ and $b$ are the specific
write-read pair we are determining visibility), and quantified variables within
each disjunction ($x$ and $y$, etc.) are the bound variables to help establish
the $\text{vis}$ relation between fixed parameters $a$ and $b$. Thus, instead of
writing it as $\text{viewed} \subseteq ar$, it should rather be
$(b, a) \in \text{viewed} => (a, b) \in \text{ar}$.

#### [Reviewers A, B, C] Comments about more extensively using examples for explanations and improving the presentation.

We will reflect the comment in the revision.

#### [Reviewer B] What is the “custom” type of operation, and why is it needed?

Operation custom type(s) and the (optional) functionality to add more fields to
`Operation` sort globally are for users to define their own DM(s) beyond what we
already provide.

#### [Reviewer B] Is it realistic to expect that developers are familiar with axiomatic semantics and SMT encodings?

As mentioned in BQ-2 and BQ-3, our tool targets developers working on critical
distributed systems where correctness justifies additional modeling effort,
requiring basic understanding of distributed systems theory and satisfiability
modulo theories. However, the community has observed increasing interest in
automated theorem solving, with more schools offering formal verification and
logic courses. We expect growing familiarity with these concepts among
developers. Importantly, our tool is significantly easier to use than full
formal verification frameworks like Verus, Dafny, Rocq, or Lean where users
specify high-level consistency constraints rather than writing detailed proofs
or implementation (code level) verification.

#### [Reviewer C] The can-view relation could be simplified. Perhaps it makes sense to additionally provide a logically reduced definition, that also takes advantage of the invariant $rtime \ge stime$?

We agree the formalization can be simplified. We will reflect this comment in
the revision.

#### [Reviewer C] It may be more comfortable for the reader if the order of the arrow relation is swapped.

We were following the notation used in prior work [9, 37], but we acknowledge
this change would help with the overall flow and intuitiveness. We will reflect
this comment in the revision.

#### [Reviewer C] L565 is difficult to understand.

We will make it more understandable in the revision. In the meantime, the
detailed concepts are documented with inline comments in our implementation
`consistency/abstract_execution.py`.

# Review #998D

## Metareview

Dear authors, thank you for your submission to ICSE'26. The reviewers carefully
discussed your rebuttal letter. While they find the presented method of checking
the compatibility between the application logic and systems' guarantees
promising, several concerns remained, as detailed below:

1. How can the framework be used?: The response does not provide additional
   information beyond what is already in the paper, but it confirms the
   reviewer's understanding that the users need to manually create an AppGraph
   instance using the provided library. Moreover, the task and difficulty of
   writing AppGraph remain unclear. The reviewers would have appreciated more
   details on when the AppGraphs are created, when they are modified, when
   analysis is triggered, and who is responsible for managing them (lead
   developer, architect?).

2. What is the benefit for software engineers, and how can it be assessed?:
   While the reviewers find the response useful, it underscores the fact that
   the benefits of the approach are not clearly demonstrated in the current
   submission.

3. What is the cost/overhead for software engineers, and how can it be assessed?
   Although the response emphasizes the lines of code involved, the reviewers
   are concerned that the real cost lies in the learning curve required to
   understand and utilize the notation. This seems to require a formal
   background for users to effectively use the framework.

We hope the feedback will help in preparing an improved version of the paper.

## Recommendation

1. Reject
