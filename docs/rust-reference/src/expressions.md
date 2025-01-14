# Expressions

> **<sup>Syntax</sup>**\
> _Expression_ : ... | _Lifetime_ | `typeid` `(` _Type_ `)`

The syntax of expressions in annotations is the same as in Rust code, with two additional supported forms:
- A lifetime parameter in scope may be used as an expression. This denotes the RustBelt `lifetime_t` value corresponding to that lifetime parameter.
- The expression `typeid(T)` denotes the typeid of type T.

Also, certain Rust expressions are interpreted differently in annotations than in Rust code:
- Array expressions are interpreted as `list<T>` values. For example, `[10, 20, 30]` is interpreted as `cons(10, cons(20, cons(30, nil)))`.
- Arithmetic expressions on integer types are interpreted as operations on the mathematical set ℤ of all integers; they produce their mathematical result and never wrap around.

Note that `match` expressions may be used to perform case analysis on values of VeriFast inductive types.
