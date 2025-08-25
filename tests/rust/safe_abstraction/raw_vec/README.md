# Partial verification of RawVec with VeriFast

With certain [caveats](#caveats), this proof proves functional correctness as well as [soundness](https://doc.rust-lang.org/nomicon/working-with-unsafe.html) of RawVec associated functions `new_in`, `with_capacity_in`, `ptr`, `capacity`, `try_reserve`, `try_reserve_exact`, and `drop`, RawVecInner associated functions `new_in`, `with_capacity_in`, `try_allocate_in`, `ptr`, `non_null`, `capacity`, and `needs_to_grow`, and functions `capacity_overflow`, `handle_error`, `alloc_guard`, and `layout_array`, as well as functional correctness of RawVec associated functions `into_box`, `from_raw_parts_in`, `from_nonnull_in`, RawVecInner associated functions `from_raw_parts_in`, `from_nonnull_in`, `current_memory`, `try_reserve`, `try_reserve_exact`, `set_ptr_and_cap`, `grow_amortized`, `grow_exact`, `shrink`, `shrink_unchecked`, and `deallocate`, and functions `new_cap` and `finish_grow`.

## What is RawVec?

RawVec is an internal abstraction used in the implementation of Rust's Vec and VecDeque data structures. RawVec's job is to take care of the allocation, deallocation, growing, and shrinking of the buffer used by Vec and VecDeque to store the elements. It hides the complexities of correctly dealing with a zero-sized element type, with a zero-capacity buffer, with possible arithmetic overflows, etc. It does not call the allocator for zero-size buffers.

RawVec is defined as follows:

```rust
type Cap = core::num::niche_types::UsizeNoHighBit;

struct RawVecInner<A: Allocator = Global> {
    ptr: Unique<u8>,
    cap: Cap,
    alloc: A,
}

pub(crate) struct RawVec<T, A: Allocator = Global> {
    inner: RawVecInner<A>,
    _marker: PhantomData<T>,
}
```

RawVecInner is like RawVec, but only generic over the allocator, not the element type. Therefore, all RawVecInner methods take the element layout as a parameter. Having this separation reduces the amount of code that needs to be monomorphized.

The `cap` field is a `UsizeNoHighBit`, which is like a `usize` except that its high bit must always be 0. In other words, its value must always be between 0 and `isize::MAX`. This allows the compiler to use the high bit for niche optimizations. The `cap` field's value is used only for non-zero-size element types; if T is a ZST, the field value is ignored and the logical capacity is `usize::MAX`.

## Tour of the proof

### Predicates RawVecInner and RawVec

The core definitions of the proof are the following:

```
fix logical_capacity(cap: UsizeNoHighBit, elem_size: usize) -> usize {
    if elem_size == 0 { usize::MAX } else { cap.as_inner() }
}

pred RawVecInner<A>(t: thread_id_t, self: RawVecInner<A>, elemLayout: Layout, alloc_id: alloc_id_t, ptr: *u8, capacity: usize) =
    Allocator(t, self.alloc, alloc_id) &*&
    capacity == logical_capacity(self.cap, elemLayout.size()) &*&
    ptr == self.ptr.as_non_null_ptr().as_ptr() &*&
    ptr as usize % elemLayout.align() == 0 &*&
    pointer_within_limits(ptr) == true &*&
    if capacity * elemLayout.size() == 0 {
        true
    } else {
        elemLayout.repeat(capacity) == some(pair(?allocLayout, ?stride)) &*&
        alloc_block_in(alloc_id, ptr, allocLayout)
    };

pred RawVec<T, A>(t: thread_id_t, self: RawVec<T, A>, alloc_id: alloc_id_t, ptr: *T, capacity: usize) =
    RawVecInner(t, self.inner, Layout::new::<T>, alloc_id, ?ptr_, capacity) &*& ptr == ptr_ as *T;
```

These are three VeriFast *ghost declarations*.
- The first defines *fixpoint function* `logical_capacity`. A fixpoint function is a pure mathematical function; it must always terminate, must not have side-effects, and must not depend on the state of memory.
- The second defines *predicate* `RawVecInner`. A predicate is a named, parameterized separation logic assertion. Abstractly speaking, assertion `RawVecInner(t, self, elemLayout, alloc_id, ptr, capacity)` asserts exclusive ownership of RawVecInner value `self`, accessible to thread `t` (in case allocator type A is not Send), valid with respect to element layout `elemLayout`, using the allocator identified by `alloc_id`, with buffer pointer `ptr` and logical capacity `capacity`. (Note that a value `alloc` of a type A : Allocator is not a good identifier for the allocator, since `alloc` and `&alloc` are different values that denote the same allocator.) Concretely, among other things, the body of the predicate asserts exclusive ownership of the `A` value `self.alloc`, accessible to thread `t` and denoting the allocator identified by `alloc_id`; it also asserts that the pointer is properly aligned for the element layout and, if the buffer size is nonzero, exclusive permission (denoted by the `alloc_block_in` predicate) to deallocate or reallocate (grow or shrink) the allocation at `ptr`, whose layout is given by pure function `Layout::repeat`. The notation `?allocLayout` denotes a *binding occurrence* of logical variable `allocLayout`. This variable is bound at this point through pattern matching against the result of `elemLayout.repeat(capacity)`. The `&*&` operator denotes *separating conjunction*; it asserts the resources asserted by the left-hand side and, *separately*, the resources asserted by the right-hand side. For example, `alloc_block_in(alloc_id, ptr, allocLayout) &*& alloc_block_in(alloc_id, ptr, allocLayout)` is unsatisfiable because it asserts *two* copies of resource `alloc_block_in(alloc_id, ptr, allocLayout)` and there can only ever be one of these, since it denotes exclusive permission to deallocate or reallocate the allocation.
- The third defines predicate `RawVec`. Abstractly speaking, assertion `RawVec(t, self, alloc_id, ptr, capacity)` asserts exclusive ownership of RawVec value `self`, accessible to thread `t`, using the allocator identified by `alloc_id`, with buffer pointer `ptr` and logical capacity `capacity`. It is defined trivially in terms of predicate `RawVecInner`.

### RawVecInner assocated function `new_in`

```rust
impl<A: Allocator> RawVecInner<A> {
    const fn new_in(alloc: A, align: Alignment) -> Self
    /*@
    req exists::<usize>(?elemSize) &*&
        thread_token(?t) &*&
        Allocator(t, alloc, ?alloc_id) &*&
        std::alloc::is_valid_layout(elemSize, align.as_nonzero().get()) == true;
    @*/
    /*@
    ens thread_token(t) &*&
        RawVecInner(t, result, Layout::from_size_align(elemSize, align.as_nonzero().get()), alloc_id, ?ptr, ?capacity) &*&
        array_at_lft_(alloc_id.lft, ptr, capacity * elemSize, _) &*&
        capacity * elemSize == 0;
    @*/
    //@ on_unwind_ens false;
    //@ safety_proof { ... }
    {
        let ptr = Unique::from_non_null(NonNull::without_provenance(align.as_nonzero()));
        // `cap: 0` means "unallocated". zero-sized types are ignored.
        let cap = ZERO_CAP;
        let r = Self { ptr, cap, alloc };
        //@ div_rem_nonneg_unique(align.as_nonzero().get(), align.as_nonzero().get(), 1, 0);
        //@ let layout = Layout::from_size_align(elemSize, align.as_nonzero().get());
        //@ close RawVecInner(t, r, layout, alloc_id, _, _);
        r
    }
}
```

This function creates and returns a RawVecInner value, accessible to the current thread `t` and valid with respect to an element layout with the given alignment and any element size `elemSize` that, together with the given alignment, constitutes a [valid layout](https://doc.rust-lang.org/beta/std/alloc/struct.Layout.html). It uses the allocator denoted by `alloc`. The precondition (given by the `req` clause) asserts the `thread_token` for the current thread `t`, which denotes exclusive permission to access resources that are only accessible to thread `t`. Furthermore, the precondition also asserts ownership of `alloc`. The `thread_token` is also asserted by the postcondition (given by the `ens` clause), but ownership of `alloc` is not. It follows that the caller loses ownership of `alloc`, but gains ownership of the RawVecInner value. The postcondition also asserts an `array_at_lft_` resource. It denotes ownership of a possibly uninitialized region of memory at `ptr` of size `capacity * elemSize`, but only until the end of the allocator's lifetime `alloc_id.lft`. The size is always zero in this case, so this resource is really an empty box, but asserting it here allows the caller to treat the case of a zero-size allocation uniformly with the case of a nonzero-size one.

This function never unwinds, so its unwind postcondition (given by the `on_unwind_ens` clause) is `false`. We did not in fact verify unwind paths (we invoked VeriFast with the `-ignore_unwind_paths` option), so we will ignore unwind postconditions in the remainder of this tour.

The proof calls lemma [`div_rem_nonneg_unique`](https://github.com/verifast/verifast/blob/d44166ebe72b2846b1a4464dc0ad52fe69c647a9/bin/rust/prelude_core.rsspec#L67) to help VeriFast see that `ptr` is properly aligned for the given alignment. It then uses the `close` ghost command to wrap the resources described by predicate `RawVecInner` into a `RawVecInner` *chunk* in VeriFast's symbolic heap. In this case, the only resource described by this predicate is the ownership of `alloc`. In this case, therefore, the `close` command *consumes* the `Allocator(t, alloc, alloc_id)` chunk from the symbolic heap and *produces* a `RawVecInner(t, r, layout, alloc_id, ptr_, capacity)` chunk, for some values for `ptr_` and `capacity` which VeriFast derives from the definition of `RawVecInner`. At this point, VeriFast also checks that the facts asserted by the `RawVecInner` predicate hold.

For every Rust function not marked as `unsafe`, VeriFast generates a specification (i.e. a precondition and a postcondition) that expresses the function's *semantic well-typedness*, which guarantees that calling this function from safe code cannot cause undefined behavior. By default, VeriFast checks that the specification written by the user trivially implies the generated specification. For function `new_in`, however, that is not the case. In that case, the user must provide a `safety_proof` clause proving that the written specification implies the generated specification. We postpone the topic of semantic well-typedness for now and will discuss these safety proofs later.

### Function `layout_array`

The definition of function `layout_array` in the Rust standard library is as follows:

```rust
fn layout_array(cap: usize, elem_layout: Layout) -> Result<Layout, TryReserveError> {
    elem_layout.repeat(cap).map(|(layout, _pad)| layout).map_err(|_| CapacityOverflow.into())
}
```

The verified version is as follows:

```rust
fn layout_array(cap: usize, elem_layout: Layout) -> Result<Layout, TryReserveError>
//@ req thread_token(currentThread);
/*@
ens thread_token(currentThread) &*&
    match result {
        Result::Ok(layout) => elem_layout.repeat(cap) == some(pair(layout, ?stride)),
        Result::Err(err) => <std::collections::TryReserveError>.own(currentThread, err)
    };
@*/
//@ safety_proof { ... }
{
    let r = match elem_layout.repeat(cap) {
        Ok(info) => Ok(info.0),
        Err(err) => Err(err)
    };
    let r2 = match r {
        Ok(l) => Ok(l),
        Err(err) => {
            let e = CapacityOverflow;
            //@ close <std::collections::TryReserveErrorKind>.own(currentThread, e);
            Err(e.into())
        }
    };
    r2
}
```

Since VeriFast does not currently support verifying code that involves lambda expressions, we inlined the calls of `Result::map` and `Result::map_err`. We developed a tool called `refinement-checker`, that ships with VeriFast. We use it to check that the original version of `raw_vec` *refines* the verified version, which means that every behavior of the original version is also a behavior of the verified version. Therefore, if we can prove through verification that the verified version has no undefined behavior, then it follows that neither does the original version.

The postcondition performs a case analysis on the result of the function. If the function returns `Err(err)`, the postcondition asserts *ownership* of TryReserveError value `err` accessible to the current thread, using notation `<TryReserveError>.own(currentThread, err)`.

The function calls [`<TryReserveErrorKind as Into<TryReserveError>>::into`](https://github.com/verifast/verifast/blob/2e7dd7a6d1aef2c9ffe7a1cedcbe28463f02440b/bin/rust/std/lib.rsspec#L1697), whose precondition asserts `<TryReserveErrorKind>.own(currentThread, e)`. This chunk is created using the `close` ghost command. TryReserveErrorKind is an [enum](https://doc.rust-lang.org/std/collections/enum.TryReserveErrorKind.html); its ownership predicate (automatically generated by VeriFast) simply asserts ownership of the relevant constructor's fields. Since CapacityOverflow has no fields, in this case closing the predicate does not consume anything.

Since function `layout_array` is not marked as `unsafe`, VeriFast generates a specification for it that expresses its semantic well-typedness. The generated specification mostly simply asserts ownership of the arguments in the precondition, and ownership of the result in the postcondition. In this case, it is as follows:
```rust
fn layout_array(cap: usize, elem_layout: Layout) -> Result<Layout, TryReserveError>
//@ req thread_token(currentThread) &*& <Layout>.own(currentThread, elem_layouyt);
//@ ens thread_token(currentThread) &*& <Result<Layout, TryReserveError>>.own(currentThread, result);
```
(As an optimization, VeriFast skips asserting ownership of types like `usize` whose ownership it knows to be trivial.)

VeriFast cannot automatically prove that the written specification implies the generated specification, so we provide a `safety_proof` clause:
```rust
/*@
safety_proof {
    leak <Layout>.own(_t, elem_layout);
    let result = call();
    match result {
        Result::Ok(layout) => { std::alloc::close_Layout_own(_t, layout); }
        Result::Err(e) => {}
    }
    close <std::result::Result<Layout, std::collections::TryReserveError>>.own(_t, result);
}
@*/
```
A safety proof is a block of ghost commands, one of which must be `call()`. VeriFast verifies the block against the generated specification, using the written specification to symbolically execute the `call()`.

The safety proof for function `layout_array` first leaks the ownership of `elem_layout`. Ownership of a Layout value does not assert any resources, but unfortunately VeriFast does not currently realize that automatically so without the `leak` command it would complain that the proof might leak resources.

After performing the `call()`, the proof must produce ownership of the Result value. It does so using the `close` command, but first it must produce ownership of the Result constructor's field. In the `Err` case, it gets it directly from the `call()`'s postcondition, but in the `Ok` case it must create it by calling lemma [`std::alloc::close_Layout_own`](https://github.com/verifast/verifast/blob/2e7dd7a6d1aef2c9ffe7a1cedcbe28463f02440b/bin/rust/std/lib.rsspec#L691).

### RawVecInner associated function `try_allocate_in`

#### Specification

The proof for this function is rather large. Let's first focus on the specification:

```rust
enum AllocInit {
    Uninitialized,
    Zeroed,
}

impl<A: Allocator> RawVecInner<A> {
    fn try_allocate_in(
        capacity: usize,
        init: AllocInit,
        alloc: A,
        elem_layout: Layout,
    ) -> Result<Self, TryReserveError>
    /*@
    req thread_token(?t) &*&
        Allocator(t, alloc, ?alloc_id) &*&
        t == currentThread;
    @*/
    /*@
    ens thread_token(t) &*&
        match result {
            Result::Ok(v) =>
                RawVecInner(t, v, elem_layout, alloc_id, ?ptr, ?capacity_) &*&
                capacity <= capacity_ &*&
                match init {
                    raw_vec::AllocInit::Uninitialized =>
                        array_at_lft_(alloc_id.lft, ptr, ?n, _) &*&
                        elem_layout.size() % elem_layout.align() != 0 || n == capacity_ * elem_layout.size(),
                    raw_vec::AllocInit::Zeroed =>
                        array_at_lft(alloc_id.lft, ptr, ?n, ?bs) &*&
                        elem_layout.size() % elem_layout.align() != 0 || n == capacity_ * elem_layout.size() &*&
                        forall(bs, (eq)(0)) == true
                },
            Result::Err(e) => <std::collections::TryReserveError>.own(t, e)
        };
    @*/
    //@ safety_proof { ... }
```
The postcondition asserts that, if the function succeeds, it returns a RawVecInner value with a capacity that is at least the requested capacity. Furthermore, it returns ownership of a region of memory, whose size `n` equals the product of the capacity and the element size, at least if the given element layout's size is a multiple of its alignment. (If that is not the case, the block will be larger, but since the only client of RawVecInner only passes element layouts that satisfy this property, we did not bother to specify that.) If an uninitialized buffer was requested, the region will be possibly uninitialized, as expressed by predicate `array_at_lft_` (notice the trailing underscore), and if a zeroed buffer was requested, the region will be initialized (as expressed by predicate `array_at_lft`) with a list of bytes `bs` that satisfies `forall(bs, (eq)(0)) == true`, expressed using fixpoint functions [`forall`](https://github.com/verifast/verifast/blob/2e7dd7a6d1aef2c9ffe7a1cedcbe28463f02440b/bin/rust/list.rsspec#L156) and [`eq`](https://github.com/verifast/verifast/blob/2e7dd7a6d1aef2c9ffe7a1cedcbe28463f02440b/bin/rust/prelude_core_core.rsspec#L5) defined in the VeriFast prelude.

#### First part

Let's go over the proof part by part. The first part calls `layout_array` to compute the layout for the allocation:
```rust
{
    //@ std::alloc::Layout_inv(elem_layout);
    
    // We avoid `unwrap_or_else` here because it bloats the amount of
    // LLVM IR generated.
    let layout = match layout_array(capacity, elem_layout) {
        Ok(layout) => layout,
        Err(_) => {
            //@ leak <std::collections::TryReserveError>.own(_, _);
            //@ std::alloc::Allocator_to_own(alloc);
            //@ close <std::collections::TryReserveErrorKind>.own(currentThread, std::collections::TryReserveErrorKind::CapacityOverflow);
            return Err(CapacityOverflow.into())
        },
    };
```
The proof first calls [`std::alloc::Layout_inv`](https://github.com/verifast/verifast/blob/2e7dd7a6d1aef2c9ffe7a1cedcbe28463f02440b/bin/rust/std/lib.rsspec#L716) to make VeriFast aware of the fact that a Layout is always valid, meaning, roughly speaking, that its size is at most `isize::MAX`.

If `layout_array` returns an error, `alloc` will get dropped, which VeriFast treats like a call of [`std::ptr::drop_in_place`](https://github.com/verifast/verifast/blob/2e7dd7a6d1aef2c9ffe7a1cedcbe28463f02440b/bin/rust/std/lib.rsspec#L488). This call requires `<A>.own(currentThread, alloc)`, but all we have (from our precondition) is `Allocator(currentThread, alloc, alloc_id)`. We convert one into the other using lemma [`std::alloc::Allocator_to_own`](https://github.com/verifast/verifast/blob/2e7dd7a6d1aef2c9ffe7a1cedcbe28463f02440b/bin/rust/std/lib.rsspec#L842).

#### Second part

The second part handles the case of a zero-size layout:
```rust
//@ let elemLayout = elem_layout;
//@ let layout_ = layout;
//@ assert elemLayout.repeat(capacity) == some(pair(layout_, ?stride));
//@ std::alloc::Layout_repeat_some(elemLayout, capacity);
//@ mul_mono_l(elemLayout.size(), stride, capacity);
// Don't allocate here because `Drop` will not deallocate when `capacity` is 0.
if layout.size() == 0 {
    let elem_layout_alignment = elem_layout.alignment();
    //@ close exists(elem_layout.size());
    let r = Self::new_in(alloc, elem_layout_alignment);
    //@ RawVecInner_inv2::<A>();
    //@ assert RawVecInner(_, _, _, _, ?ptr_, ?capacity_);
    //@ mul_mono_l(0, capacity, elem_layout.size());
    //@ mul_zero(capacity, elem_layout.size());
    /*@
    match init {
        raw_vec::AllocInit::Uninitialized => { close array_at_lft_(alloc_id.lft, ptr_, 0, []); }
        raw_vec::AllocInit::Zeroed => { close array_at_lft(alloc_id.lft, ptr_, 0, []); }
    }
    @*/
    return Ok(r);
}
```
The proof starts by loading `elem_layout` and `layout` into ghost variables. This is necessary to be able mention them
in the subsequent `assert` command, because `elem_layout` and `layout` have their address taken, so loading them accesses
the VeriFast symbolic heap, and expressions that access the symbolic heap are not allowed inside assertions.

Next, the proof uses an `assert` command to bind the `layout`'s stride (the offset between subsequent array elements) to ghost variable `stride`.
The stride is equal to the element size, except if the element size is not a multiple of the element alignment.
It then calls lemma [`std::alloc::Layout_repeat_some`](https://github.com/verifast/verifast/blob/2e7dd7a6d1aef2c9ffe7a1cedcbe28463f02440b/bin/rust/std/lib.rsspec#L732)
to make VeriFast aware of the properties of the stride, including that it is at least the element size.
It then calls lemma [`mul_mono_l`](https://github.com/verifast/verifast/blob/2e7dd7a6d1aef2c9ffe7a1cedcbe28463f02440b/bin/rust/prelude_core.rsspec#L55)
to derive that `elemLayout.size() * capacity <= stride * capacity`.

If the layout size is zero, the code calls `Self::new_in`. Its precondition requires an [`exists`](https://github.com/verifast/verifast/blob/2e7dd7a6d1aef2c9ffe7a1cedcbe28463f02440b/bin/rust/prelude_core.rsspec#L29) chunk, so the proof creates it using a `close` command. After the
`new_in` call, it calls lemma `RawVecInner_inv2`, defined near the top of the `raw_vec.rs` proof as follows:
```
lem RawVecInner_inv2<A>()
    req RawVecInner::<A>(?t, ?self_, ?elemLayout, ?alloc_id, ?ptr, ?capacity);
    ens RawVecInner::<A>(t, self_, elemLayout, alloc_id, ptr, capacity) &*&
        pointer_within_limits(ptr) == true &*& ptr as usize % elemLayout.align() == 0 &*&
        0 <= capacity &*& capacity <= usize::MAX &*&
        if elemLayout.size() == 0 { capacity == usize::MAX } else { capacity <= isize::MAX };
{
    open RawVecInner(t, self_, elemLayout, alloc_id, ptr, capacity);
    std::num::niche_types::UsizeNoHighBit_inv(self_.cap);
    close RawVecInner(t, self_, elemLayout, alloc_id, ptr, capacity);
}
```
A lemma is like a regular Rust function, except that it is defined inside an annotation, and VeriFast checks that it has no side-effects and terminates.
The proof of the lemma uses an `open` command, which consumes the specified predicate chunk and produces the predicate's definition. In this case, the
point of the `open` command is to make VeriFast aware of the facts asserted by the predicate. Any resources produced by the `open` command are consumed
again by the subsequent `close` command.

#### Third part

Next, the function allocates a block of memory with the computed layout:
```rust
let result = match init {
    AllocInit::Uninitialized => {
        let r;
        //@ let alloc_ref = precreate_ref(&alloc);
        //@ let k = begin_lifetime();
        unsafe {
            //@ let_lft 'a = k;
            //@ std::alloc::init_ref_Allocator_at_lifetime::<'a, A>(alloc_ref);
            r = alloc.allocate(layout);
            //@ leak Allocator(_, _, _);
        }
        //@ end_lifetime(k);
        //@ std::alloc::end_ref_Allocator_at_lifetime::<A>();
        r
    }
    AllocInit::Zeroed => { ... }
};
```
Here, the proof is complicated by the fact that VeriFast verifies compliance with Rust's rule saying that memory pointed to by a shared reference must not be mutated while the shared reference is active. VeriFast does so by, first of all, treating the shared reference as denoting a *different place* from the original place from which the shared reference was created. While both places have the same address, they have different *provenances*. It follows that any separation logic permissions the proof has for accessing the original place do not apply to the new place. Secondly, VeriFast forces the proof to *precreate* and *initialize* the new shared reference. Initializing generally means producing permission to perform accesses through the shared reference, and taking away permission to mutate the original place (except in the presence of interior mutability). Finally, *ending* a shared reference removes all permissions to perform accesses through the shared reference and restores permission to mutate the original place.

Since Allocator method [`allocate`](https://github.com/verifast/verifast/blob/2e7dd7a6d1aef2c9ffe7a1cedcbe28463f02440b/bin/rust/std/lib.rsspec#L982) takes a shared reference to the Allocator value, the line `r = alloc.allocate(layout);` implicitly creates a shared reference to variable `alloc`. VeriFast treats a shared reference creation like a call of function [`create_ref`](https://github.com/verifast/verifast/blob/2e7dd7a6d1aef2c9ffe7a1cedcbe28463f02440b/bin/rust/aliasing.rsspec#L87). That function's precondition requires a `ref_precreated_token`, which can only be obtained using lemma
[`precreate_ref`](https://github.com/verifast/verifast/blob/2e7dd7a6d1aef2c9ffe7a1cedcbe28463f02440b/bin/rust/aliasing.rsspec#L77). This lemma also produces a `ref_init_perm`, which the proof needs to initialize the new shared reference. The proof performs the initialization using lemma [`init_ref_Allocator_at_lifetime`](https://github.com/verifast/verifast/blob/2e7dd7a6d1aef2c9ffe7a1cedcbe28463f02440b/bin/rust/std/lib.rsspec#L908), which produces the `ref_initialized` resource required by `create_ref`, but also consumes `Allocator::<A>(currentThread, alloc, alloc_id)` and produces `Allocator::<&'a A>(currentThread, alloc_ref, alloc_id)`, for some lifetime variable `'a`. It also produces a token that allows the proof to recover the original `Allocator` chunk using lemma [`end_ref_Allocator_at_lifetime`](https://github.com/verifast/verifast/blob/2e7dd7a6d1aef2c9ffe7a1cedcbe28463f02440b/bin/rust/std/lib.rsspec#L913) after lifetime `'a` has ended. The proof first uses [`begin_lifetime`](https://github.com/verifast/verifast/blob/2e7dd7a6d1aef2c9ffe7a1cedcbe28463f02440b/bin/rust/rust_belt/lifetime_logic.rsspec#L71) to create a semantic lifetime, and then uses ghost declaration `let_lft` to introduce a lifetime variable `'a` at the level of the type system, bound to semantic lifetime `k`, whose scope is the enclosing block. After the block, the proof uses [`end_lifetime`](https://github.com/verifast/verifast/blob/2e7dd7a6d1aef2c9ffe7a1cedcbe28463f02440b/bin/rust/rust_belt/lifetime_logic.rsspec#L76) to obtain the `lifetime_dead_token` needed by `end_ref_Allocator_at_lifetime`.

#### Fourth part

The final part of the `try_allocate_in` proof involves no new concepts:
```rust
    let ptr = match result {
        Ok(ptr) => ptr,
        Err(_) => {
            //@ std::alloc::Allocator_to_own(alloc);
            let err1 = AllocError { layout, non_exhaustive: () };
            //@ std::alloc::close_Layout_own(currentThread, layout);
            //@ close_tuple_0_own(currentThread);
            //@ close <std::collections::TryReserveErrorKind>.own(currentThread, err1);
            return Err(err1.into())
        }
    };

    // Allocators currently return a `NonNull<[u8]>` whose length
    // matches the size requested. If that ever changes, the capacity
    // here should change to `ptr.len() / size_of::<T>()`.
    /*@
    if elem_layout.size() % elem_layout.align() == 0 {
        div_rem_nonneg(elem_layout.size(), elem_layout.align());
        div_rem_nonneg(stride, elem_layout.align());
        if elem_layout.size() / elem_layout.align() < stride / elem_layout.align() {
            mul_mono_l(elem_layout.size() / elem_layout.align() + 1, stride / elem_layout.align(), elem_layout.align());
        } else {
            if elem_layout.size() / elem_layout.align() > stride / elem_layout.align() {
                mul_mono_l(stride / elem_layout.align() + 1, elem_layout.size() / elem_layout.align(), elem_layout.align());
                assert false;
            }
        }
        assert stride == elem_layout.size();
    }
    @*/
    /*@
    if elem_layout.size() == 0 {
        div_rem_nonneg_unique(elem_layout.size(), elem_layout.align(), 0, 0);
        assert false;
    }
    @*/
    //@ mul_mono_l(1, elem_layout.size(), capacity);
    let res = Self {
        ptr: Unique::from(ptr.cast()),
        cap: unsafe { Cap::new_unchecked(capacity) },
        alloc,
    };
    //@ std::alloc::alloc_block_in_aligned(ptr.ptr.as_ptr());
    //@ close RawVecInner(t, res, elem_layout, alloc_id, ptr.ptr.as_ptr(), _);
    Ok(res)
}
```

### Predicate `RawVecInner_share_`

Rust knows two types of ownership: *exclusive ownership*, as in the case of a non-borrowed value or a mutable reference; and *shared ownership*, as in the case of a shared reference.
Correspondingly, predicate `RawVecInner(t, self, elemLayout, alloc_id, ptr, capacity)` denotes *exclusive ownership* of a RawVecInner value `self`, and predicate `RawVecInner_share_(k, t, l, elemLayout, alloc_id, ptr, capacity)` denotes *shared ownership* with lifetime `k` of the place of type RawVecInner at `l` and the value it stores.
Shared references are Copy and therefore duplicable; correspondingly, `RawVecInner_share_` is duplicable as well.

```
pred_ctor RawVecInner_frac_borrow_content<A>(l: *RawVecInner<A>, elemLayout: Layout, ptr: *u8, capacity: usize)(;) =
    struct_RawVecInner_padding(l) &*&
    (*l).ptr |-> ?u &*&
    (*l).cap |-> ?cap &*&
    capacity == logical_capacity(cap, elemLayout.size()) &*&
    ptr == u.as_non_null_ptr().as_ptr() &*&
    ptr as usize % elemLayout.align() == 0 &*&
    pointer_within_limits(ptr) == true &*&
    if capacity * elemLayout.size() == 0 {
        true
    } else {
        elemLayout.repeat(capacity) == some(pair(?allocLayout, ?stride))
    };

pred RawVecInner_share_<A>(k: lifetime_t, t: thread_id_t, l: *RawVecInner<A>, elemLayout: Layout, alloc_id: alloc_id_t, ptr: *u8, capacity: usize) =
    [_]std::alloc::Allocator_share(k, t, &(*l).alloc, alloc_id) &*&
    [_]frac_borrow(k, RawVecInner_frac_borrow_content(l, elemLayout, ptr, capacity)) &*& ptr != 0;
```

Predicate `RawVecInner_share_` uses two predicates in its definition:
- `[_]Allocator_share::<A>(k, t, l, alloc_id)` denotes shared ownership of the place of type A at `l` and the Allocator value stored at that place, at lifetime `k`, accessible to thread `t`, denoting allocator `alloc_id`. The `[_]` prefix indicates that this is a *dummy fraction*, which means it is duplicable. VeriFast automatically duplicates a dummy fraction when it is consumed, so that it is never actually removed from the symbolic heap.
- `[_]frac_borrow(k, p)` denotes a *fractured borrow* of the resources asserted by *predicate value* `p` at lifetime `k`. Owning a fractured borrow allows the owner to obtain *fractional ownership* of payload `p` until the end of lifetime `k`. Fractional ownership of a memory region is sufficient for reading, but writing requires exclusive ownership.

Predicate `RawVecInner_share_` specifies the payload of the fractured borrow by means of *predicate constructor* `RawVecInner_frac_borrow_content`. A predicate constructor has two parameter lists. Applying a predicate constructor to arguments for the first parameter list yields a *predicate value* which can be passed as an argument to a higher-order predicate such as `frac_borrow`.

`RawVecInner_frac_borrow_content(l, elemLayout, ptr, capacity)()` asserts ownership of the struct padding at `l` and the `ptr` and `cap` fields at `l`, the latter expressed using *points-to assertions*: assertion `place |-> value` asserts ownership of place `place` and furthermore asserts that it currently stores value `value`.

### Lemma `share_RawVecInner`

```
pred RawVecInner_share_end_token<A>(k: lifetime_t, t: thread_id_t, l: *RawVecInner<A>, elemLayout: Layout, alloc_id: alloc_id_t, ptr: *u8, capacity: usize) =
    borrow_end_token(k, std::alloc::Allocator_full_borrow_content_(t, &(*l).alloc, alloc_id)) &*&
    borrow_end_token(k, RawVecInner_frac_borrow_content(l, elemLayout, ptr, capacity)) &*&
    if capacity * elemLayout.size() == 0 {
        true
    } else {
        elemLayout.repeat(capacity) == some(pair(?allocLayout, ?stride)) &*&
        alloc_block_in(alloc_id, ptr, allocLayout)
    };

lem share_RawVecInner<A>(k: lifetime_t, l: *RawVecInner<A>)
    nonghost_callers_only
    req [?q]lifetime_token(k) &*&
        *l |-> ?self_ &*&
        RawVecInner(?t, self_, ?elemLayout, ?alloc_id, ?ptr, ?capacity);
    ens [q]lifetime_token(k) &*&
        [_]RawVecInner_share_(k, t, l, elemLayout, alloc_id, ptr, capacity) &*&
        RawVecInner_share_end_token(k, t, l, elemLayout, alloc_id, ptr, capacity);
{
    open RawVecInner(t, self_, elemLayout, alloc_id, ptr, capacity);
    close RawVecInner_frac_borrow_content::<A>(l, elemLayout, ptr, capacity)();
    borrow(k, RawVecInner_frac_borrow_content(l, elemLayout, ptr, capacity));
    full_borrow_into_frac(k, RawVecInner_frac_borrow_content(l, elemLayout, ptr, capacity));
    std::alloc::close_Allocator_full_borrow_content_(t, &(*l).alloc);
    borrow(k, std::alloc::Allocator_full_borrow_content_(t, &(*l).alloc, alloc_id));
    std::alloc::share_Allocator_full_borrow_content_(k, t, &(*l).alloc, alloc_id);
    close RawVecInner_share_(k, t, l, elemLayout, alloc_id, ptr, capacity);
    close RawVecInner_share_end_token(k, t, l, elemLayout, alloc_id, ptr, capacity);
    leak RawVecInner_share_(k, t, l, elemLayout, alloc_id, ptr, capacity);
}

lem end_share_RawVecInner<A>(l: *RawVecInner<A>)
    nonghost_callers_only
    req RawVecInner_share_end_token(?k, ?t, l, ?elemLayout, ?alloc_id, ?ptr, ?capacity) &*& [_]lifetime_dead_token(k);
    ens *l |-> ?self_ &*& RawVecInner(t, self_, elemLayout, alloc_id, ptr, capacity);
{
    open RawVecInner_share_end_token(k, t, l, elemLayout, alloc_id, ptr, capacity);
    borrow_end(k, std::alloc::Allocator_full_borrow_content_(t, &(*l).alloc, alloc_id));
    std::alloc::open_Allocator_full_borrow_content_(t, &(*l).alloc, alloc_id);
    borrow_end(k, RawVecInner_frac_borrow_content(l, elemLayout, ptr, capacity));
    open RawVecInner_frac_borrow_content::<A>(l, elemLayout, ptr, capacity)();
    close RawVecInner(t, *l, elemLayout, alloc_id, ptr, capacity);
}
```

Lemma `share_RawVecInner` converts exclusive ownership of a place of type RawVecInner, and the value it stores, to shared ownership at a lifetime `k`. This is possible only if the lifetime is alive, as evidenced by the existence of the `lifetime_token` for `k`. Specifically, the caller must show a *fraction* `q` (a real number greater than zero and not greater than one) of the lifetime token for `k`. (The lifetime token for a lifetime is produced by [`begin_lifetime`](https://github.com/verifast/verifast/blob/2e7dd7a6d1aef2c9ffe7a1cedcbe28463f02440b/bin/rust/rust_belt/lifetime_logic.rsspec#L71) and consumed by [`end_lifetime`](https://github.com/verifast/verifast/blob/2e7dd7a6d1aef2c9ffe7a1cedcbe28463f02440b/bin/rust/rust_belt/lifetime_logic.rsspec#L76).) The lemma also produces a `RawVecInner_share_end_token` that the caller can pass to lemma `end_share_RawVecInner` after `k` has ended to recover exclusive ownership.

The proof first uses the `open` command to replace the `RawVecInner` chunk in the symbolic heap by its contents. It then uses the `close` command to create a chunk whose predicate is the predicate value `RawVecInner_frac_borrow_content(l, elemLayout, ptr, capacity)`. It then calls [`borrow`](https://github.com/verifast/verifast/blob/2e7dd7a6d1aef2c9ffe7a1cedcbe28463f02440b/bin/rust/rust_belt/lifetime_logic.rsspec#L117) to create a *full borrow* at lifetime `k` with payload `RawVecInner_frac_borrow_content(l, elemLayout, ptr, capacity)`. A full borrow denotes exclusive ownership of the payload, but only until the end of the lifetime. This lemma also produces a `borrow_end_token` that allows the caller to recover the payload free and clear after the lifetime has ended. The proof then uses [`full_borrow_into_frac`](https://github.com/verifast/verifast/blob/2e7dd7a6d1aef2c9ffe7a1cedcbe28463f02440b/bin/rust/rust_belt/lifetime_logic.rsspec#L262) to turn the full borrow into a fractured borrow. 

It then uses lemma [`close_Allocator_full_borrow_content`](https://github.com/verifast/verifast/blob/2e7dd7a6d1aef2c9ffe7a1cedcbe28463f02440b/bin/rust/std/lib.rsspec#L852) to wrap ownership of the `alloc` field, and the Allocator value it stores, into a chunk whose predicate is `Allocator_full_borrow_content_(t, &(*l).alloc, alloc_id)`. It then creates a full borrow with this predicate value as its payload. Then it uses [`share_Allocator_full_borrow_content`](https://github.com/verifast/verifast/blob/2e7dd7a6d1aef2c9ffe7a1cedcbe28463f02440b/bin/rust/std/lib.rsspec#L860) to produce the `Allocator_share` chunk that the proof needs in order to create the `RawVecInner_share_` chunk. After creating this chunk as well as the `RawVecInner_share_end_token` chunk, the proof finishes by using the `leak` command to turn full ownership of the `RawVecInner_share_` chunk into a *dummy fraction chunk* `[_]RawVecInner_share_(...)`. (This command is called `leak` because it silences the leak error that VeriFast normally generates if chunks are left in the symbolic heap at the end of a function, after consuming the postcondition. Specifically: VeriFast generates a leak error only if *non-dummy-fraction* chunks are left in the symbolic heap.)

Lemma `end_share_RawVecInner` uses lemmas [`borrow_end`](https://github.com/verifast/verifast/blob/2e7dd7a6d1aef2c9ffe7a1cedcbe28463f02440b/bin/rust/rust_belt/lifetime_logic.rsspec#L122) and [`open_Allocator_full_borrow_content_`](https://github.com/verifast/verifast/blob/2e7dd7a6d1aef2c9ffe7a1cedcbe28463f02440b/bin/rust/std/lib.rsspec#L856) to recover exclusive ownership of the RawVecInner object.

### RawVecInner associated function `non_null`

```rust
impl<A: Allocator> RawVecInner<A> {
    const fn non_null<T>(&self) -> NonNull<T>
    //@ req [_]RawVecInner_share_(?k, ?t, self, ?elem_layout, ?alloc_id, ?ptr, ?capacity) &*& [?q]lifetime_token(k);
    //@ ens [q]lifetime_token(k) &*& result.as_ptr() == ptr as *T;
    //@ safety_proof { ... }
    {
        //@ open RawVecInner_share_(k, t, self, elem_layout, alloc_id, ptr, capacity);
        //@ open_frac_borrow(k, RawVecInner_frac_borrow_content(self, elem_layout, ptr, capacity), q);
        //@ open [?f]RawVecInner_frac_borrow_content::<A>(self, elem_layout, ptr, capacity)();
        let r = self.ptr.cast().as_non_null_ptr();
        //@ close [f]RawVecInner_frac_borrow_content::<A>(self, elem_layout, ptr, capacity)();
        //@ close_frac_borrow(f, RawVecInner_frac_borrow_content(self, elem_layout, ptr, capacity));
        r
    }
}
```

This function's precondition asserts shared ownership of `self` at some lifetime `k`, and a fraction of the lifetime token for `k`. The postcondition asserts the latter as well. (The function does not bother to return the shared ownership; the caller can duplicate it anyway.)

The proof uses lemma [`open_frac_borrow`](https://github.com/verifast/verifast/blob/2e7dd7a6d1aef2c9ffe7a1cedcbe28463f02440b/bin/rust/rust_belt/lifetime_logic.rsspec#L275) to obtain fractional ownership at some fraction `f` of the fractured borrow's payload. This is sufficient to read (but not write) the `ptr` field. Notice that `open_frac_borrow` consumes a fraction, with coefficient given by its third argument, of the lifetime token for `k`. Indeed, accessing a fractured borrow is possible only while its lifetime is alive. Since the proof must return to the caller the fraction `q` of the lifetime token that it received from the caller, it is forced to call lemma [`close_frac_borrow`](https://github.com/verifast/verifast/blob/2e7dd7a6d1aef2c9ffe7a1cedcbe28463f02440b/bin/rust/rust_belt/lifetime_logic.rsspec#L280) to recover the lifetime token fraction. This lemma consumes the payload fraction `f` that was produced by `open_frac_borrow`.

### Lemma `init_ref_RawVecInner_`

We first look at this lemma's specification, and then at the two parts of its proof.

```
lem init_ref_RawVecInner_<A>(l: *RawVecInner<A>)
    nonghost_callers_only
    req ref_init_perm(l, ?l0) &*&
        [_]RawVecInner_share_(?k, ?t, l0, ?elemLayout, ?alloc_id, ?ptr, ?capacity) &*&
        [?q]lifetime_token(k);
    ens [q]lifetime_token(k) &*&
        [_]RawVecInner_share_(k, t, l, elemLayout, alloc_id, ptr, capacity) &*&
        [_]frac_borrow(k, ref_initialized_(l));
```

This lemma allows the caller to initialize a precreated shared reference `l` to a RawVecInner place at `l0`. (Remember that initializing a shared reference means enabling read access through the shared reference, and disabling write access to the original place.) Given shared ownership of `l0`, it produces shared ownership at `l`. It also produces proof that the shared reference has been initialized, and will remain so for the duration of lifetime `k`, in the form of a `ref_initialized(l)` token wrapped into a predicate value of type `pred(;)` using the [`ref_initialized_`](https://github.com/verifast/verifast/blob/c01806aa35cb4efb20b721a41611406acf0d784c/bin/rust/aliasing.rsspec#L40) predicate constructor, which in turn is wrapped into a fractured borrow at lifetime `k`.

Initializing the shared reference means, among other things, *consuming* fractional ownership of the `(*l0).ptr` and `(*l0).cap` fields. But ownership of these fields is being borrowed at some lifetime. Crucially, when the lifetime ends, the resources that were borrowed must again be available to the lender. Therefore, consuming borrowed resources is allowed only if the consumption is *reversible*. More specifically, if one opens a fractured borrow using lemma [`open_frac_borrow`](https://github.com/verifast/verifast/blob/2e7dd7a6d1aef2c9ffe7a1cedcbe28463f02440b/bin/rust/rust_belt/lifetime_logic.rsspec#L275), the *same* payload predicate that was produced by `open_frac_borrow` will be consumed by [`close_frac_borrow`](https://github.com/verifast/verifast/blob/2e7dd7a6d1aef2c9ffe7a1cedcbe28463f02440b/bin/rust/rust_belt/lifetime_logic.rsspec#L280) when the lifetime token fraction is recovered. It follows that the pair of lemmas `open_frac_borrow`/`close_frac_borrow` is not suitable for the `init_ref_RawVecInner` proof. Instead, we use the more flexible pair [`open_frac_borrow_strong_`](https://github.com/verifast/verifast/blob/e829d5aaa295ed63b278e86ce694914f983f2d65/bin/rust/rust_belt/lifetime_logic.rsspec#L346)/[`close_frac_borrow_strong_`](https://github.com/verifast/verifast/blob/e829d5aaa295ed63b278e86ce694914f983f2d65/bin/rust/rust_belt/lifetime_logic.rsspec#L355). Crucially, the payload predicate `Q` consumed by `close_frac_borrow_strong_` need *not* be the same as the predicate `P` produced by `open_frac_borrow_strong_`, provided that a *restoring lemma* can be proven that converts `Q` back into `P`. Conceptually, the lifetime logic infrastructure will call this lemma when the lifetime ends to restore the resources to the form that the lender expects.

#### First part

We will now look at the part of the proof that initializes the shared reference and prepares the new payload for the fractured borrow. Then we will look at the part that proves the restoring lemma, closes the fractured borrow, and produces the lemma's postcondition.

```
{
    open_ref_init_perm_RawVecInner(l);
    open RawVecInner_share_(k, t, l0, elemLayout, alloc_id, ptr, capacity);
    std::alloc::init_ref_Allocator_share(k, t, &(*l).alloc);
    frac_borrow_sep(k, RawVecInner_frac_borrow_content(l0, elemLayout, ptr, capacity), ref_initialized_(&(*l).alloc));
    open_frac_borrow_strong_(
        k,
        sep_(RawVecInner_frac_borrow_content(l0, elemLayout, ptr, capacity), ref_initialized_(&(*l).alloc)),
        q);
    open [?f]sep_(RawVecInner_frac_borrow_content(l0, elemLayout, ptr, capacity), ref_initialized_(&(*l).alloc))();
    open [f]RawVecInner_frac_borrow_content::<A>(l0, elemLayout, ptr, capacity)();
    open [f]ref_initialized_::<A>(&(*l).alloc)();
    let ptr_ = (*l0).ptr;
    let cap_ = (*l0).cap;
    init_ref_readonly(&(*l).ptr, 1/2);
    init_ref_readonly(&(*l).cap, 1/2);
    init_ref_padding_RawVecInner(l, 1/2);
    {
        pred P() = ref_padding_initialized(l);
        close [1 - f]P();
        close_ref_initialized_RawVecInner(l);
        open P();
    }
    close [f/2]RawVecInner_frac_borrow_content::<A>(l, elemLayout, ptr, capacity)();
    close scaledp(f/2, RawVecInner_frac_borrow_content(l, elemLayout, ptr, capacity))();
    close [f]ref_initialized_::<RawVecInner<A>>(l)();
    close scaledp(f, ref_initialized_(l))();
    close sep_(scaledp(f/2, RawVecInner_frac_borrow_content(l, elemLayout, ptr, capacity)), scaledp(f, ref_initialized_(l)))();
```

First, the proof converts the `ref_init_perm` for the RawVecInner object into a separate `ref_init_perm` for each of the fields (`ptr`, `cap`, and `alloc`), as well as a `ref_padding_init_perm`, giving permission to initialize the struct's padding bytes. For each struct S defined by the program, VeriFast introduces a lemma `open_ref_init_perm_S`, which performs this conversion.

Then, it calls lemma [`init_ref_Allocator_share`](https://github.com/verifast/verifast/blob/c01806aa35cb4efb20b721a41611406acf0d784c/bin/rust/std/lib.rsspec#L881) to initialize the `alloc` field. This produces a `[_]frac_borrow(k, ref_initialized_(&(*l).alloc))` chunk, proving that this field has now been initialized, and will remain so until the end of lifetime `k`. Next, the proof calls lemma [`frac_borrow_sep`](https://github.com/verifast/verifast/blob/c01806aa35cb4efb20b721a41611406acf0d784c/bin/rust/rust_belt/lifetime_logic.rsspec#L318) to join the `[_]frac_borrow(k, RawVecInner_frac_borrow_content(l0, elemLayout, ptr, capacity))` chunk (obtained from the `RawVecInner_share_` chunk) and the `[_]frac_borrow(k, ref_initialized_(&(*l).alloc))` chunk into one `[_]frac_borrow(k, sep_(RawVecInner_frac_borrow_content(l0, elemLayout, ptr, capacity), ref_initialized_(&(*l).alloc)))` chunk (expressed using predicate constructor [`sep_`](https://github.com/verifast/verifast/blob/c01806aa35cb4efb20b721a41611406acf0d784c/bin/rust/rust_belt/lifetime_logic.rsspec#L312)). This is necessary because we need both of these payloads together to obtain the (fraction of a) `ref_initialized(l)` token that we need to produce (wrapped in a `frac_borrow`) to show that the RawVecInner object has been initialized. The proof then calls [`open_frac_borrow_strong_`](https://github.com/verifast/verifast/blob/e829d5aaa295ed63b278e86ce694914f983f2d65/bin/rust/rust_belt/lifetime_logic.rsspec#L346) to get fractional access at a fraction `f` to the combined payload, in a way that will allow the proof to specify a *different* payload predicate when closing the borrow back up.

After opening the payload predicates, the proof stores the values of the `ptr` and `cap` fields into ghost variables, for use in assertions the second part of the proof. (Expressions that access resources are not allowed inside assertions.) Then, the proof uses lemma [`init_ref_readonly`](https://github.com/verifast/verifast/blob/c01806aa35cb4efb20b721a41611406acf0d784c/bin/rust/aliasing.rsspec#L45) to initialize the `ptr` and `cap` fields, and lemma `init_ref_padding_RawVecInner` to initialize the padding. (Such a lemma is introduced by VeriFast for each struct defined by the program.) Both lemmas take as an argument a coefficient C (which must be greater than 0 and less than 1) such that if a fraction `f` of the ownership of the original place is available, a fraction `C*f` is transferred to the reference being initialized. This enables read access through the new reference, and disables write access to the original place.

At this point, the proof has the following resources (among others): `ref_initialized(&(*l).ptr)`, `ref_initialized(&(*l).cap)`, `[f]ref_initialized(&(*l).alloc)`, and `ref_padding_initialized(l)`. It then uses `close_ref_initialized_RawVecInner` to consume `[f]ref_initialized(&(*l).ptr)`, `[f]ref_initialized(&(*l).cap)`, `[f]ref_initialized(&(*l).alloc)`, and `[f]ref_padding_initialized(l)` and produce `[f]ref_initialized(l)`. (Such a lemma is introduced by VeriFast for each struct defined by the program.) However, this lemma takes the coefficient for the fractions to be produced and consumed from the coefficient of the `ref_padding_initialized` chunk it finds in the symbolic heap. Therefore, the proof needs to *hide* a fraction `1 - f` of the `ref_padding_initialized` chunk from this lemma. It does so by introducing a local predicate `P` and temporarily wrapping that fraction inside that predicate.

The proof then wraps up the payloads to be consumed when closing the fractured borrow into the appropriate payload predicates, but scaled by appropriate coefficients using predicate constructor [`scaledp`](https://github.com/verifast/verifast/blob/e829d5aaa295ed63b278e86ce694914f983f2d65/bin/rust/rust_belt/lifetime_logic.rsspec#L322).

#### Second part

```
    {
        pred Ctx() =
            ref_padding_end_token(l, l0, f/2) &*& [f/2]struct_RawVecInner_padding(l0) &*& [1 - f]ref_padding_initialized(l) &*&
            ref_readonly_end_token(&(*l).ptr, &(*l0).ptr, f/2) &*& [f/2](*l0).ptr |-> ptr_ &*& [1 - f]ref_initialized(&(*l).ptr) &*&
            ref_readonly_end_token(&(*l).cap, &(*l0).cap, f/2) &*& [f/2](*l0).cap |-> cap_ &*& [1 - f]ref_initialized(&(*l).cap);
        close Ctx();
        produce_lem_ptr_chunk restore_frac_borrow(
                Ctx,
                sep_(scaledp(f/2, RawVecInner_frac_borrow_content(l, elemLayout, ptr, capacity)), scaledp(f, ref_initialized_(l))),
                f,
                sep_(RawVecInner_frac_borrow_content(l0, elemLayout, ptr, capacity), ref_initialized_(&(*l).alloc)))() {
            open sep_(scaledp(f/2, RawVecInner_frac_borrow_content(l, elemLayout, ptr, capacity)), scaledp(f, ref_initialized_(l)))();
            open scaledp(f/2, RawVecInner_frac_borrow_content(l, elemLayout, ptr, capacity))();
            open RawVecInner_frac_borrow_content::<A>(l, elemLayout, ptr, capacity)();
            open scaledp(f, ref_initialized_(l))();
            open ref_initialized_::<RawVecInner<A>>(l)();
            open Ctx();
            open_ref_initialized_RawVecInner(l);
            end_ref_readonly(&(*l).ptr);
            end_ref_readonly(&(*l).cap);
            end_ref_padding_RawVecInner(l);
            close [f]RawVecInner_frac_borrow_content::<A>(l0, elemLayout, ptr, capacity)();
            close [f]ref_initialized_::<A>(&(*l).alloc)();
            close [f]sep_(RawVecInner_frac_borrow_content(l0, elemLayout, ptr, capacity), ref_initialized_(&(*l).alloc))();
        } {
            close_frac_borrow_strong_();
        }
    }
    full_borrow_into_frac(k, sep_(scaledp(f/2, RawVecInner_frac_borrow_content(l, elemLayout, ptr, capacity)), scaledp(f, ref_initialized_(l))));
    frac_borrow_split(k, scaledp(f/2, RawVecInner_frac_borrow_content(l, elemLayout, ptr, capacity)), scaledp(f, ref_initialized_(l)));
    frac_borrow_implies_scaled(k, f/2, RawVecInner_frac_borrow_content(l, elemLayout, ptr, capacity));
    frac_borrow_implies_scaled(k, f, ref_initialized_(l));
    close RawVecInner_share_(k, t, l, elemLayout, alloc_id, ptr, capacity);
    leak RawVecInner_share_(k, t, l, elemLayout, alloc_id, ptr, capacity);
}
```

The proof is now ready to call [`close_frac_borrow_strong_`](https://github.com/verifast/verifast/blob/e829d5aaa295ed63b278e86ce694914f983f2d65/bin/rust/rust_belt/lifetime_logic.rsspec#L355), except that it still needs to prove the *restoring lemma* that shows that the new payload predicate can be converted back into the original payload predicate when the lifetime ends. More accurately, `close_frac_borrow_strong_` consumes the new payload predicate `Q` as well as a *context* predicate `Ctx`; the restoring lemma must show that `Ctx() &*& Q()` can be converted back into `[f]P()` where `P` is original payload predicate and `f` is the fraction of `P` that was produced by `open_frac_borrow_strong_`. The context predicate captures the resources that are not needed for the new payload but that will be needed to convert the new payload predicate back into the old payload predicate. The present proof uses a local predicate `Ctx` for this context predicate.

Lemma `close_frac_borrow_strong_` requires the restoring lemma to be proven. More specifically, it requires an `is_restore_frac_borrow` chunk, which serves as evidence that a lemma satisfying *lemma type* [`restore_frac_borrow`](https://github.com/verifast/verifast/blob/e829d5aaa295ed63b278e86ce694914f983f2d65/bin/rust/rust_belt/lifetime_logic.rsspec#L351) has been proven. More generally, an `is_T` predicate is introduced by VeriFast for each *lemma type* `T`. An `is_T` chunk can be produced using a `produce_lem_ptr_chunk T(lemTypeArgs)(lemParams) { Proof } { Client }` ghost command, specifying arguments `lemTypeArgs` for the lemma type parameters, parameter names `lemParams` for the lemma parameters, and two blocks of ghost code: a block `Proof` that proves a lemma that satisfies the lemma type, and a block `Client` that can use the `is_T` chunk. The `is_T` chunk is produced at the start of `Client` and consumed at the end. (Consuming the `is_T` chunk at the end of `Client` is necessary for preventing infinite recursion through lemma pointers.)

The proof of the restoring lemma opens the payload predicates and the context predicate. It then calls `open_ref_initialized_RawVecInner` to turn the `[f]ref_initialized(l)` chunk back into chunks for the fields and for the padding. It then uses `end_ref_readonly` and `end_ref_padding_RawVecInner` to transfer the fractional ownership at `l` back to `l0`. At that point the original payload predicates can be closed up.

The `Client` block of the `produce_lem_ptr_chunk` ghost command simply calls `close_frac_borrow_strong_`. This lemma produces a full borrow, which is turned into a fractured borrow using [`full_borrow_into_frac`](https://github.com/verifast/verifast/blob/e829d5aaa295ed63b278e86ce694914f983f2d65/bin/rust/rust_belt/lifetime_logic.rsspec#L262). The resulting fractured borrow is split into two using [`frac_borrow_split`](https://github.com/verifast/verifast/blob/e829d5aaa295ed63b278e86ce694914f983f2d65/bin/rust/rust_belt/lifetime_logic.rsspec#L314). At this point, the proof has two fractured borrows, each of whose payloads is scaled by some coefficient. The coefficients are dropped using lemma [`frac_borrow_implies_scaled`](https://github.com/verifast/verifast/blob/e829d5aaa295ed63b278e86ce694914f983f2d65/bin/rust/rust_belt/lifetime_logic.rsspec#L324).

## Caveats

First of all, this proof was performed with the following VeriFast command-line flags:
- `-skip_specless_fns`: VeriFast ignores the functions that do not have a `req` or `ens` clause.
- `-ignore_unwind_paths`: This proof ignores code that is reachable only when unwinding.
- `-allow_assume`: This proof uses a number of `assume` ghost statements and `assume_correct` clauses. These must be carefully audited.

Secondly, since VeriFast uses the `rustc` frontend, which assumes a particular target architecture, VeriFast's results hold only for the used Rust toolchain's target architecture. When VeriFast reports "0 errors found" for a Rust program, it always reports the targeted architecture as well (e.g. `0 errors found (2149 statements verified) (target: x86_64-unknown-linux-gnu (LP64))`).

Thirdly, VeriFast has a number of [known unsoundnesses](https://github.com/verifast/verifast/issues?q=is%3Aissue+is%3Aopen+label%3Aunsoundness) (reasons why VeriFast might in some cases incorrectly accept a program), including the following:
- VeriFast does not yet fully verify compliance with Rust's [pointer aliasing rules](https://doc.rust-lang.org/reference/behavior-considered-undefined.html).
- VeriFast does not yet properly verify compliance of custom type interpretations with Rust's [variance](https://doc.rust-lang.org/reference/subtyping.html#variance) rules.

Fourthly, unlike foundational tools such as [RefinedRust](https://plv.mpi-sws.org/refinedrust/), VeriFast has not itself been verified, so there are undoubtedly also unknown unsoundnesses. Such unsoundnesses might exist in VeriFast's [symbolic execution engine](https://github.com/model-checking/verify-rust-std/issues/213#issuecomment-2531006855) [itself](https://github.com/model-checking/verify-rust-std/issues/213#issuecomment-2534922580) or in its [prelude](https://github.com/verifast/verifast/tree/master/bin/rust) (definitions and axioms automatically imported at the start of every verification run) or in the [specifications](https://github.com/verifast/verifast/blob/master/bin/rust/std/lib.rsspec) it uses for the Rust standard library functions called by the program being verified.
