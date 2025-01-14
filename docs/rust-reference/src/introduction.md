# Introduction

VeriFast is a tool for modular formal verification of the absence of [undefined
behavior](https://doc.rust-lang.org/reference/behavior-considered-undefined.html)
in Rust[^other-languages] programs that use `unsafe` blocks and the
[soundness](https://doc.rust-lang.org/nomicon/working-with-unsafe.html) of Rust
modules that use `unsafe` blocks. It works by _symbolically executing_ each
function separately, using a _separation logic_ representation of memory,
starting from a symbolic state that represents an arbitrary program state that
satisfies the function's _precondition_, and checking that each state at which
the function returns satisfies the function's _postcondition_. By using the
callee's precondition and postcondition instead of its body when symbolically
executing a function call, and by using the user-specified loop invariant when
symbolically executing a loop so as to be able to symbolically execute the loop
body only once, and by using _symbols_ to represent possibly infinitely many
program states using a finite number of symbolic states, VeriFast covers all
(usually infinitely many) possible executions of a function using a finite (and
usually small) number of symbolic executions, allowing the verification of
(small) programs to usually complete in a matter of seconds.

For functions not declared as `unsafe`, VeriFast derives a precondition and
postcondition from the function's parameter types and return type using the
separation logic interpretation of Rust's types defined by
[RustBelt](https://research.ralfj.de/thesis.html); for functions declared as
`unsafe`, the user has to provide a precondition and postcondition by inserting
specially marked comments called _annotations_ into the source code. Similarly, for each loop a loop
invariant has to be provided in an annotation. To be able to
express these conditions (called _assertions_), the user may generally also have
to insert annotations defining mathematical recursive datatypes called
_inductive datatypes_, mathematical recursive functions over these datatypes
called _fixpoint functions_, recursive named separation logic assertions called
_predicates_, and _type predicates_ defining a custom interpretation for some of the
struct types defined by the current module (as well as some less common constructs
such as _VeriFast named function types_, _lemma function types_, _predicate
families_, and _predicate family instances_).

In order for symbolic execution to succeed, the user may furthermore have to
insert annotations containing _ghost commands_ such as `open` and `close`
commands for unfolding and folding predicates and calls of _lemma functions_,
possibly recursive functions defined inside annotations that are checked by
VeriFast to terminate and to not have side-effects and that serve as possibly
inductive proofs about fixpoint functions and predicates.

This reference defines the syntax of the various kinds of annotations, and
describes VeriFast's symbolic execution algorithm and the various checks that
VeriFast performs.

## The state of VeriFast

VeriFast has been developed by Bart Jacobs, Jan Smans, and Frank Piessens at KU
Leuven, Department of Computer Science, DistriNet research group since 2008,
with many contributions from contributors inside and outside DistriNet. VeriFast
for Rust has been developed by Nima Rahimi Foroushaani and Bart Jacobs at
DistriNet since 2022. The lead developer and main maintainer is Bart Jacobs, an
associate professor at DistriNet, who combines these activities with his usual
research, education, and service duties. The largest verification performed so far with
VeriFast for Rust, the verification of certain properties of certain functions
of the Rust standard library's LinkedList data structure, was performed in
December 2024. Its support for the Rust language is as of yet very incomplete[^other-languages-incomplete],
so that for any new nontrivial use case, it is to be expected, for now, that the
tool will have to be extended. Bart Jacobs is eager to support anyone interested
in using VeriFast. However, despite his best intentions, he may get distracted
by other occupations; in that case, please do not hesitate to remind him early
and often---your continued showing of interest will only delight him and you may
rest assured that, given sufficient prodding, your issue will be resolved eventually.

## The state of this reference

This reference is under construction; much material is still missing. Please
bear with us! But if there are particular parts you're particularly eager to
see, it always helps to let us know.

[^other-languages]: VeriFast also supports (subsets of) C and Java.
[^other-languages-incomplete]: as is its support for Java and, to a somewhat lesser extent, C