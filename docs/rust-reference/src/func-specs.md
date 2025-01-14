# Function specifications

VeriFast accepts the following *specification clauses* between a function's header and its body:

> **<sup>Syntax</sup>**\
> _SpecificationClause_ :\
> &nbsp;&nbsp; &nbsp;&nbsp; `/*@` `req` _Assertion_ `;` `@*/`\
> &nbsp;&nbsp; | `/*@` `ens` _Assertion_ `;` `@*/` \
> &nbsp;&nbsp; | `/*@` `assume_correct` `@*/`

Note that VeriFast also support single-line annotations of the form `//@ ...annotation...`. Such an annotation is entirely equivalent to `/*@ ...annotation... @*/`.

Notice that the requires clause and the ensures clause must be in separate annotations.
