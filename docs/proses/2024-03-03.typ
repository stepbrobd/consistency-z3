= Modeling Consistency Semantics with Predicate Logic

In Viotti et al. @viotti2016consistency, the authors provided structured
overview of different consistency notions that appeared in distributed systems.
Building upon the work of Viotti et al., we propose to use predicate logic
formulas derived from the definitions of consistency notions, to model multiple
consistency semantics, and reason about the compositional properties of these
semantics with Z3 SMT solver @demoura2008z3.

== Basis of the Model

The premitive building blocks of our models is an operation. An operation is
defined as a type with member fields: `proc`, `type`, `obj`, `ival`, `oval`,
`stime`, and `rtime`. Same as in Viotti et al., we use `proc` to denote the
process that issued the operation, `type` to denote the type of the operation
(read or write), `obj` to denote the object that the operation is performed on,
`ival` to denote the value of the object before the operation, `oval` to denote
the value of the object after the operation (null if the operation does not
return), `stime` to denote the time when the operation is issued, and `rtime` to
denote the time when the operation is returned ($infinity$ if the operation does
not return).

In Z3, we define an operation as a `Sort` (a type) with above mentioned fields.
When defining consistency semantics, we can assign constraints to these fields
to mimic the behavior of the semantics.

== Relations

Relations are constraints between the fields of operations.


= Bibliography

#bibliography("bibliography.yml", title: none, style: "ieee")
