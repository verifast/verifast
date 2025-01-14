# Verifying non-`unsafe` functions

## RustBelt

A core value proposition of Rust is that well-typed programs have no undefined behavior, under certain conditions on the use of `unsafe` blocks. The [RustBelt](https://plv.mpi-sws.org/rustbelt/) project has developed a mathematically precise proposal for what those conditions are. In this proposal, a *semantics* is defined for Rust's types and typing judgments in *separation logic*, providing a definition of whether a function is *semantically well-typed* that talks only about the function's *behavior*, not about its precise syntactic structure, and is therefore applicable to functions containing `unsafe` blocks. They have proven the soundness of Rust's type checker with respect to this semantics, implying that if a function that does not contain `unsafe` blocks is syntactically well-typed, then it is semantically well-typed. Therefore, if a program consists of modules that use `unsafe` blocks and client code that does not, it suffices to establish that these modules are semantically well-typed to be able to conclude that the program as a whole is semantically well-typed and therefore has no undefined behavior.[^rustbelt-limitations]

In order to be able to express the semantics of mutable references and shared references, as well as the semantics of many of the uses of *interior mutability* in the Rust standard library, the RustBelt authors have proposed the *lifetime logic*, which defines separation logic concepts such as *lifetime tokens*, *full borrows*, *fractured borrows*, *thread tokens*, and *nonatomic borrows*.

An excellent resource for learning more about the RustBelt proposal and the advanced separation logic Iris that underlies it is [Ralf Jung's thesis](https://research.ralfj.de/thesis.html).

[^rustbelt-limitations]: More accurately speaking, the RustBelt authors have defined semantic well-typedness for a somewhat simplified version of Rust called lambda-Rust, and have proven soundness of lambda-Rust's type checker, which is a simplified version of that of Rust. Notable aspects not taken into account in the original RustBelt work include destructors (`drop`), unwinding, and Rust's aliasing rules.

## RustBelt and the lifetime logic in VeriFast

An axiomatisation of the lifetime logic into VeriFast's logic and some further RustBelt-related definitions and axioms can be found in the following files:
- [`bin/rust/rust_belt/lifetime_logic.rsspec`](https://github.com/verifast/verifast/blob/master/bin/rust/rust_belt/lifetime_logic.rsspec)
- [`bin/rust/rust_belt/general.rsspec`](https://github.com/verifast/verifast/blob/master/bin/rust/rust_belt/general.rsspec)

## Semantic well-typedness of functions in VeriFast

If a crate under verification defines a function not marked as `unsafe`, VeriFast generates a specification for that function that expresses the function's semantic well-typedness. If the function is annotated with an explicit specification as well, VeriFast first verifies that the explicit specification implies the generated one, and then verifies the function body against the explicit specification; otherwise, VeriFast verifies the function body against the generated specification.

For a function `fn f<'a, 'b : 'a, T, U>(x1: T1, ..., xN: TN) -> U`, the generated specification is as follows:
```
req thread_token(?_t) &*&
    [?_q_a]lifetime_token('a) &*&
    [?_q_b]lifetime_token('b) &*& 
    lifetime_inclusion('a, 'b) == true &*&
    <T1>.own(_t, x1) &*&
    ...
    <TN>.own(_t, xN);
ens thread_token(_t) &*&
    [_q_a]lifetime_token('a) &*&
    [_q_b]lifetime_token('b) &*&
    <U>.own(_t, result);
```

### Drop functions

If the crate under verification implements Drop for a struct `S<'a>` with fields `f1 : T1` through `fN : TN`, VeriFast generates the following specification for `drop(&mut self)`:
```
req thread_token(?_t) &*&
    [?_q_a]lifetime_token('a) &*&
    <S>.full_borrow_content(_t, self);
ens thread_token(_t) &*&
    [_q_a]lifetime_token('a) &*&
    <T1>.full_borrow_content(_t, &(*self).f1) &*&
    ...
    <TN>.full_borrow_content(_t, &(*self).fN);
```

## Semantics of types in VeriFast

For simple types T such as `bool` and the integer types, we simply have `<T>.own(t, x) = true`. Here are some more interesting cases:
- `<&'a mut T>.own(t, l) = full_borrow('a, <T>.full_borrow_content(t, l))`
- `<&'a T>.own(t, l) = <T>.share('a, t, l)`

For any type T, we have `<T>.full_borrow_content(t, l) = *l |-> ?x &*& <T>.own(t, x)`.

For simple types T such as `bool` and the integer types, we simply have `<T>.share(k, t, l) = frac_borrow(k, <T>.full_borrow_content(t, l))`.

If the crate under verification defines a struct S, it can define a custom semantics for type S by defining the `<S>.own` and `<S>.share` predicates.[^struct_preds] If it does so, it must also prove a number of *proof obligations* about these predicates.

[^struct_preds]: Note: as part of processing a type predicate definition `pred <S>.p(xs) = A;`, VeriFast introduces a predicate definition `pred S_p(xs) = A;`. Therefore, `<S>.own` and `S_own` are equivalent, and so are `<S>.share` and `S_share`.

### Proof obligations for `own`

If a crate defines a struct S as well as a custom definition of `<S>.own`, and the struct's field types are not trivially droppable and the struct does not implement the Drop trait, then the crate must prove the following lemma:

```
lem S_drop()
    req S_own(?t, ?s);
    ens <T1>.own(t, s.f1) &*& ... &*& <Tn>.own(t, s.fn);
```
where the fields of S are `f1` through `fn` and their types are T1 through Tn.

If a crate defines a struct S as well as a custom definition of `<S>.own`, and S is Send, and the `own` predicate mentions the thread id, then the crate must prove the following lemma:

```
lem S_send(t1: thread_id_t)
    req S_own(?t, ?s);
    ens S_own(t1, s);
```

### Proof obligations for `share`

If a crate defines a struct S as well as a custom definition of `<S>.share`, then the crate must prove the following two lemmas:

```
lem S_share_full(k: lifetime_t, t: thread_id_t, l: *S)
    req atomic_mask(Nlft) &*& [?q]lifetime_token(k) &*& full_borrow(k, S_full_borrow_content(t, l));
    ens atomic_mask(Nlft) &*& [q]lifetime_token(k) &*& [_]S_share(k, t, l);

lem S_share_mono(k: lifetime_t, k1: lifetime_t, t: thread_id_t, l: *S)
    req lifetime_inclusion(k1, k) == true &*& [_]S_share(k, t, l);
    ens [_]S_share(k1, t, l);
```

Additionally, if S is Sync and the share predicate mentions the thread id, then the crate must prove the following lemma:

```
lem S_sync(t1: thread_id_t)
    req [_]S_share(?k, ?t, ?l);
    ens [_]S_share(k, t1, l);
```

### Generic structs

If struct S is generic in type parameters T1 through Tm, each of the above lemmas must also be generic in the same parameters. Furthermore, they may additionally require and ensure `type_interp::<Ti>()`, for each `i`. Furthermore, if a type parameter is Send or Sync, an `is_Send(typeid(Ti)) == true` or `is_Sync(typeid(Ti)) == true` conjunct may be added to the precondition. For example:

```
lem Pair_send<A, B>(t1: thread_id_t)
    req type_interp::<A>() &*& type_interp::<B>() &*& Pair_own::<A, B>(?t, ?pair) &*& is_Send(typeid(A)) && is_Send(typeid(B));
    ens type_interp::<A>() &*& type_interp::<B>() &*& Pair_own::<A, B>(t1, pair);
{
    open Pair_own::<A, B>(t, pair);
    Send::send::<A>(t, t1, pair.fst);
    Send::send::<B>(t, t1, pair.snd);
    close Pair_own::<A, B>(t1, pair);
}
```

<div class="warning">

> Further proof obligations are necessary to ensure soundness with respect to Rust's [variance](https://doc.rust-lang.org/nomicon/subtyping.html) rules. VeriFast currently generates an `S_own_mono` proof obligation but its design has known problems. There are plans for an improved design but this is future work. See [#610](https://github.com/verifast/verifast/issues/610).

</div>
