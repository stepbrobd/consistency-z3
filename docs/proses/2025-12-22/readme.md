## Reviewer A:

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
[addressed] Line 574: Typo in “strainghtforward”\
[addressed] Line 647: “and” could use a different font.

Q1: What inputs does the user exactly provide to the framework to model their
application constraints?\
Q2: What is the scalability of the method to large-scale programs?\
Q3: Are the source code and evaluation data for SemantiX available?

## Reviewer B:

- Problem formulation can be improved
- Missing information regarding the use of the framework by developers
- Questionable relevance/impact (related to the above)
- Evaluation targeting initial feasibility only, not usability from actual
  stakeholders
- Presentation can be improved (grammar, figures)

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
