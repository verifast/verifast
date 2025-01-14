# Types

Inside annotations, the syntax of types is extended as follows:

> **<sup>Syntax</sup>**\
> _Type_ :\
> &nbsp;&nbsp; &nbsp;&nbsp; ... | `*_` | `any` | _PureFunctionType_ | _PredicateType_ | `real`
>
> _PureFunctionType_ :\
> &nbsp;&nbsp; &nbsp;&nbsp; `fix` `(` ( _ParamType_ `,` )<sup>*</sup> _ParamType_<sup>?</sup> `)`
>
> _ParamType_ :\
> &nbsp;&nbsp; &nbsp;&nbsp; (IDENTIFIER `:`)<sup>?</sup> _Type_
>
> _PredicateType_ :\
> &nbsp;&nbsp; &nbsp;&nbsp; `pred` `(` ((( _ParamType_ `,` )<sup>*</sup> _ParamType_ )<sup>?</sup> `;` )<sup>?</sup> ( _ParamType_ `,` )<sup>*</sup> _ParamType_<sup>?</sup> `)`

In addition to (some subset of) Rust's types, VeriFast supports the following types:
- Type `*_` (*pointer-to-anything*) is a pointer type implicitly convertible to any other pointer type. It is analogous to C's `void *`.
- Type `any` is the union of all inductive types that themselves contain `any` only in positive positions.
- The *pure function type* `fix(T1, ..., Tn, U)` is the type of mathematical functions taking N arguments, of types T1 through Tn, and returning a value of type U.
- The *predicate type* `pred(T1, ..., Tn)` is the type of separation logic predicates taking N arguments, of types T1 through Tn. The type `pred(T1, ..., Tn; U1, ..., Um)` is the type of *precise* separation logic predicates taking N input arguments and M output arguments.
- Type `real` is the type of real numbers. (It is mostly used for chunk coefficients and for reasoning about floating-point numbers.)

In pure function types and predicate types, parameter names may optionally be written for documentation purposes; they are ignored by VeriFast.

Note, furthermore:
- VeriFast does not distinguish between `*const T` and `*mut T` and supports the syntax `*T`. That is, VeriFast treats the type expressions `*const T`, `*mut T`, and `*T` identically.
- When used as the type of a ghost variable (e.g. a pure function parameter or return value, a predicate parameter, a lemma parameter, or a ghost cell) or as the type of an expression in an annotation, all integer types are interpreted as the mathematical type ℤ of all integers. Also, inside annotations arithmetic operations on integers are always interpreted as operations on ℤ and never wrap around.
