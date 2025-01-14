# Function body annotations

## Ghost commands

VeriFast accepts the following *ghost commands* as annotations in positions where statements are allowed in Rust code.

<div class="warning">

> VeriFast preprocesses `.rs` files to replace annotations inside function bodies by dummy `VeriFast_ghost_command();` statements.
> If an annotation inside a function body appears in a position where
> such a call is not allowed, you may get a confusing Rust compiler error.

</div>

> **<sup>Syntax</sup>**\
> _GhostCommandAnnotation_ : `/*@` _GhostCommand_ `@*/`
>
> _GhostCommand_ :\
> &nbsp;&nbsp; &nbsp;&nbsp; `open` _PredicateAssertion_ `;`\
> &nbsp;&nbsp; | `close` _PredicateAssertion_ `;`\
> &nbsp;&nbsp; | `let` IDENTIFIER `=` _Expression_ `;`\
> &nbsp;&nbsp; | `if` _Expression_ `{` _GhostCommand_ <sup>\*</sup> `}` ( `else` `{` _GhostCommand_ <sup>\*</sup> `}` )<sup>?</sup>\
> &nbsp;&nbsp; | `match` _Scrutinee_ `{` _MatchGhostCommandArm_ <sup>\*</sup> `}`\
> &nbsp;&nbsp; | `assert` _Assertion_ `;`\
> &nbsp;&nbsp; | `leak` _Assertion_ `;`\
> &nbsp;&nbsp; | `produce_lem_ptr_chunk` _TypePath_ `(` (( _Expression_ `,` )<sup>\*</sup> _Expression_ )<sup>?</sup> `)` `(` (( IDENTIFIER `,` )<sup>*</sup> IDENTIFIER )<sup>?</sup> `)` `{` _GhostCommand_ <sup>\*</sup> `}` ( `;` | `{` _GhostCommand_ <sup>\*</sup> `}` )\
> &nbsp;&nbsp; | `produce_fun_ptr_chunk` _TypePath_ `(` _Expression_ `)` `(` (( _Expression_ `,` )<sup>\*</sup> _Expression_ )<sup>?</sup> `)` `(` (( IDENTIFIER `,` )<sup>*</sup> IDENTIFIER )<sup>?</sup> `)` `{` _GhostCommand_ <sup>\*</sup> `}`\
> &nbsp;&nbsp; | `{` _GhostDeclaration_ <sup>\*</sup> _GhostCommand_ <sup>\*</sup> `}`\
> &nbsp;&nbsp; | `return` _Expression_ <sup>?</sup> `;`\
> &nbsp;&nbsp; | _Expression_ `;`

A `return` ghost command may only appear in a lemma body, not in a ghost command annotation.

## Block annotations

Additionally, a Rust block may start with one of the following VeriFast annotations:
- a loop invariant of the form `/*@` `inv` _Assertion_ `;` `@*/`
- a loop specification of the form `/*@` `req` _Assertion_ `;` `ens` _Assertion_ `;` `@*/`. Notice that here, the requires clause and the ensures clause must be in the same annotation, whereas in the case of function specifications they must be in separate annotations.
- a batch of ghost declarations of the form `/*@` _GhostDeclaration_ <sup>\*</sup> `@*/` The declarations supported in such batches are predicate definitions, lemma definitions, and local lifetime variable definitions (using `let_lft`).

## Call annotations

Furthermore, a *ghost generic argument list* annotation may be inserted between the function name and the argument list of a Rust function call, like so: `foo/*@::<'a, T>@*/`. This is necessary in cases where it is important to pass a particular lifetime as a generic argument to a function. If, for a function call, no ghost generic argument list is provided, VeriFast uses `'static` as the argument for each of the function's lifetime parameters.
