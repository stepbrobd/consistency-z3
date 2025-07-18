# Specifications

Some information here are outdated, please refer to the source code for the
latest definitions.

Framework user: a framework user is someone who provides node and edge
definitions (e.g. custom operations that should be supported originating from a
node, or precedences of operations) and relations to the consistency checker.

Operation: an operation is defined as a tuple of (from non-transactional
survey):

- `proc`: the process that issued the operation (used for session
  identification, e.g. same session constraint).
- `type`: the type of the operation (e.g. read, write. or custom).
- `obj`: the object the operation is performed on (e.g. a key in a key-value
  store).
- `ival`: operation input value (e.g. the value to be written, not used anywhere
  yet).
- `oval`: operation output value (e.g. the value read, not used anywhere yet).
- `stime`: invocation time of the operation (i.e. the time the operation was
  issued).
- `rtime`: response time of the operation (i.e. the time the operation was
  completed).

Think of an operation as a request-response pair, where the request is the
operation itself and the response is the operation itself with the response time
set (assuming the delays between the request and the response are equal for all
operations, the request takes `(rtime - stime)/2` time to be sent to the
handling node and to be processed, vice versa for the response).

(Our own interpretation) Operation does not contain the node that issued the
operation, nor the node that handled the operation. It's defined as a generic
entity that can be issued by any node and handled by any node. To add
constraints on the nodes that can issue or handle an operation, the framework
user must define nodes and edges.

History (in the actual writing, layout the actual Z3 clauses used to encode the
relational constraints): a set of operations. TODO: add relations between
operations within history (returns before, same session, session order).

Abstract execution (in the actual writing, layout the actual Z3 clauses used to
encode the relational constraints): one or more "instantiation" of history. An
abstract execution is a set of operations (i.e. history) that are further
constrained by the nondeterminism of the asynchronous environment (e.g., message
delivery order), and implementation-specific constraints (e.g., conflict
resolution policies) (from non-transactional survey). AE specific relations:
visibility, arbitration, happens before.

Relation predicates: a set of predicates that define the relations between
operations in a history (also includes those in AE). The predicates are used as
base/premise for consistency models (implementations in `relation.py`,
`history.py`, `abstract_execution.py`). In the implementation, the predicates
are singletons and will be added ad-hoc if any clause refers to them.

Node: node issues operations. Nodes with incoming edges can be perceived as
nodes that can handle operations issued by other nodes (servers). Nodes with
outgoing edges can be perceived as nodes that can issue operations that can be
handled by other nodes (clients). They can be used to define custom operations
(operations with types that are not read or write) that should be supported
originating from a node. Definitions of those custom operations must be provided
by the framework user and the clauses defining the custom operations must be
included in the node definition.

In the implementation, a node is defined as tuple of:

- `name`: the name, used to identify the node in a graph (can have any type, but
  must be unique).
- `needs`: a list of tuples of constraints. TODO
- `provs`: a list of tuples of constraints. TODO

Edge: edge connects nodes. Edges can be used to define the precedence of
operations on different nodes (one edge can only store exactly one type of
operation, if multiple types of operations are needed, multiple edges must be
defined). Definitions of those custom operations must be provided by the
framework user and the clauses defining the custom operations must be included
in the source node definition (specifically in the `needs` field).

Constraint: a constraint is a set of clauses that define the relations between
operations in a history (or abstract execution). Constraints can be used to
define the precedence of operations on the same node (e.g. the order of
operations issued by the same node). Or application-specific constraints (e.g.
assign data to operations' fields).

Graph: a directed multigraph that contains nodes and edges.

Compatible: compatibility is a relation between two consistency models. Two
consistency models are compatible if the the negation of the implication is
unsatisfiable (compatibility is not symmetric).

Composable: composition is an additional operator that combines two or more
consistency models into a single consistency model. It's represented as a direct
conjunction of the consistency models' constraints (the ordering of the
composition does not affect the result, relation predicates remain the same and
will only be added if any clause refers to them). Premise will be added as a
part of the composition, instead of being conjuncted with each node/edge, use
`z3.Solver.add` to add the premise to the solver. Framework users must defined
the premises as non-implicit constraints (i.e. don't use quantifiers like
`ForAll`, `Exists` and don't use `Implies`).
