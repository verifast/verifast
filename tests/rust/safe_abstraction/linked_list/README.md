# Partial verification of LinkedList with VeriFast

With certain caveats (see [Caveats](#caveats) below), this proof proves
[soundness](https://doc.rust-lang.org/nomicon/working-with-unsafe.html) of the
`Node` associated functions `new` and `into_element`, the `LinkedList` associated functions
`pop_front_node`, `new`, `new_in`, `iter`, `cursor_front_mut`,
`cursor_back_mut`, `len`, `clear`, `push_front`, `split_off`, and `extract_if`,
the `Iter` associated function `next`, the `CursorMut` associated functions `move_next`, `move_prev`,
`current`, and `remove_current`, and the `ExtractIf` associated function `next`.
Furthermore, since the `LinkedList` associated functions `contains`, `remove`, `retain`, `retain_mut`, and `drop` do not use `unsafe` blocks, do not mutate private fields, and call only the former functions, this proof implies their soundness as well.

## The proof

We here give a tour of the proof.

### Predicate `Nodes`

Central to the proof is predicate `Nodes`, defined as follows:

```
pred Nodes<T>(alloc_id: any, n: Option<NonNull<Node<T>>>, prev: Option<NonNull<Node<T>>>, last: Option<NonNull<Node<T>>>, next: Option<NonNull<Node<T>>>; nodes: list<NonNull<Node<T>>>) =
    if n == next {
        nodes == [] &*& last == prev
    } else {
        n == Option::Some(?n_) &*&
        alloc_block_in(alloc_id, NonNull_ptr(n_) as *u8, Layout::new_::<Node<T>>()) &*& struct_Node_padding(NonNull_ptr(n_)) &*&
        (*NonNull_ptr(n_)).prev |-> prev &*&
        (*NonNull_ptr(n_)).next |-> ?next0 &*&
        pointer_within_limits(&(*NonNull_ptr(n_)).element) == true &*&
        Nodes(alloc_id, next0, n, last, next, ?nodes0) &*&
        nodes == cons(n_, nodes0)
    };
```

It is expressed in [separation logic](https://en.wikipedia.org/wiki/Separation_logic), a logic for reasoning about ownership. It asserts ownership of the linked list nodes between `n` (inclusive) and `next` (exclusive). Furthermore, it asserts that the nodes have been allocated with the allocator identified by `alloc_id`, that the first node (if any) points to predecessor node `prev`, that the last node (if any) is `last`, and that the entire sequence of nodes is `nodes` (a [mathematical list](https://github.com/verifast/verifast/blob/37bb28bc5edb0e08e5ee8b63a9afd57e7c3b7ffd/bin/rust/list.rsspec#L16)).

If `n` is not equal to `next`, it asserts that `n` is not `None` and binds logical variable `n_` to the `NonNull` value wrapped by the `Option`. (The question mark indicates a binding occurrence of a logical variable.) Furthermore, it asserts ownership of the `alloc_block_in` chunk for `n_`, which proves the node was allocated using allocator `alloc_id`. The points-to assertion `(*NonNull_ptr(n_)).prev |-> prev` asserts ownership of `n_`'s `prev` field and asserts that its value equals the value of logical variable `prev`. The predicate calls itself recursively to assert ownership of the remaining nodes. Since the various parts are separated by a *separating conjunction* `&*&`, the predicate asserts that the remainder of the sequence of nodes does not overlap with the first node, which implies that the sequence of nodes is not cyclic.

### Lemma `Nodes_last_lemma`

The proof includes the lemma `Nodes_last_lemma`, defined as follows:

```
lem Nodes_last_lemma<T>(n: Option<NonNull<Node<T>>>)
    req Nodes::<T>(?alloc_id, n, ?prev, ?last, ?next, ?nodes);
    ens Nodes::<T>(alloc_id, n, prev, last, next, nodes) &*&
        match last {
            Option::None => n == next && prev == last && nodes == [],
            Option::Some(last_) =>
                match prev {
                    Option::None => n != next && length(nodes) > 0 && nth(length(nodes) - 1, nodes) == last_,
                    Option::Some(prev_) => nth(length(nodes), cons(prev_, nodes)) == last_
                }
        };
{
    open Nodes(alloc_id, n, prev, last, next, nodes);
    if n == next {
    } else {
        assert Nodes(_, ?next0, _, _, _, _);
        Nodes_last_lemma(next0);
    }
    close Nodes(alloc_id, n, prev, last, next, nodes);
}
```

This is a VeriFast lemma. It looks like a regular Rust function, except that it uses keyword `lem` instead of `fn` and it is inside a VeriFast annotation (a Rust comment that starts with `/*@` and ends with `@*/`). VeriFast checks that lemmas do not have side-effects and that they terminate. A lemma that passes these checks constitutes a proof that its precondition implies its postcondition. Lemma `Nodes_last_lemma` proves, among other things, that if predicate `Nodes(alloc_id, n, prev, last, next, nodes)` holds and `last == None`, then `n == next` and `prev == last` and `nodes == []`. It proves this as follows:
- First, it unfolds the definition of the `Nodes` predicate, using an `open` ghost command.
- Then, it performs a case analysis on whether `n == next`. If not:
  - It first uses an `assert` ghost statement to match against the recursive `Nodes` chunk produced by the `open` statement and bind the value for the `n` parameter to logical variable `next0`.
  - Then it calls itself recursively. VeriFast can tell that this recursion terminates because the `Nodes` chunk required by the recursive call's precondition was produced by unfolding the `Nodes` chunk required by the caller. Since all `Nodes` chunks have been constructed by folding the definition (using `close` ghost statements) a finite number of times, they can be unfolded only a finite number of times. (In mathematics, this is called "induction on the derivation of an inductively defined predicate".)
- Then, it folds up the original `Nodes` chunk again, using a `close` ghost statement.

### Function `unlink_node`

Here's the proof of `LinkedList<T, A>` associated function `unlink_node`:

```rust
unsafe fn unlink_node(&mut self, mut node: NonNull<Node<T>>)
/*@
req (*self).head |-> ?head &*& (*self).tail |-> ?tail &*&
    Nodes::<T>(?alloc_id, head, None, ?prev_, Some(node), ?nodes1) &*&
    alloc_block_in(alloc_id, NonNull_ptr(node) as *u8, Layout::new_::<Node<T>>()) &*&
    (*NonNull_ptr(node)).next |-> ?next_ &*&
    (*NonNull_ptr(node)).prev |-> prev_ &*&
    struct_Node_padding(NonNull_ptr(node)) &*&
    Nodes::<T>(alloc_id, next_, Some(node), tail, None, ?nodes2) &*&
    (*self).len |-> length(nodes1) + 1 + length(nodes2);
@*/
/*@
ens (*self).head |-> ?head1 &*& (*self).tail |-> ?tail1 &*&
    Nodes::<T>(alloc_id, head1, None, prev_, next_, nodes1) &*&
    alloc_block_in(alloc_id, NonNull_ptr(node) as *u8, Layout::new_::<Node<T>>()) &*&
    (*NonNull_ptr(node)).next |-> next_ &*&
    (*NonNull_ptr(node)).prev |-> prev_ &*&
    struct_Node_padding(NonNull_ptr(node)) &*&
    Nodes::<T>(alloc_id, next_, prev_, tail1, None, nodes2) &*&
    (*self).len |-> length(nodes1) + length(nodes2);
@*/
{
    let node = unsafe { node.as_mut() }; // this one is ours now, we can create an &mut.

    // Not creating new mutable (unique!) references overlapping `element`.
    match node.prev {
        Some(prev) => unsafe {
            //@ Nodes_last_lemma(head);
            //@ Nodes_split_off_last(head);
            //@ assert Nodes(_, head, None, ?pprev, prev_, ?nodes10);
            (*prev.as_ptr()).next = node.next;
            //@ open Nodes(alloc_id, next_, Some(node), tail, None, nodes2);
            //@ close Nodes(alloc_id, next_, Some(node), tail, None, nodes2);
            //@ close Nodes::<T>(alloc_id, next_, prev_, prev_, next_, []);
            //@ close Nodes::<T>(alloc_id, prev_, pprev, prev_, next_, [prev]);
            //@ Nodes_append_(head);
        },
        // this node is the head node
        None => {
            //@ Nodes_last_lemma(head);
            //@ open Nodes(alloc_id, head, _, _, _, nodes1);
            //@ close Nodes(alloc_id, next_, None, None, next_, []);
            self.head = node.next
        }
    };

    match node.next {
        Some(next) => unsafe {
            //@ open Nodes(alloc_id, next_, Some(node), tail, None, nodes2);
            (*next.as_ptr()).prev = node.prev;
            //@ close Nodes(alloc_id, next_, prev_, tail, None, nodes2);
        },
        // this node is the tail node
        None => {
            //@ open Nodes(alloc_id, next_, Some(node), _, _, nodes2);
            //@ close Nodes(alloc_id, next_, prev_, prev_, next_, []);
            self.tail = node.prev;
            
        }
    };

    self.len -= 1;
}
```

Since this function is marked as `unsafe`, VeriFast does not attempt to prove its soundness; it only proves that the code complies with the specification provided in the `req` and `ens` clause, i.e. that if started in a state that satisfies the precondition given in the `req` clause, it will not perform Undefined Behavior and any state in which it returns will satisfy the postcondition given in the `ens` clause. This specification is sufficient to prove soundness of functions `CursorMut::remove_current` and `ExtractIf::next`, which call `unlink_node`.

The precondition asserts that `node` is part of the well-formed linked list between `self.head` and `self.tail`; the postcondition asserts that there is again a well-formed linked list between `self.head` and `self.tail`, but that it no longer contains `node`, and that ownership of the node is now separate from that linked list, so that the node can be deallocated safely.

The proof invokes `Nodes_last_lemma`, as well as two other lemmas, `Nodes_split_off_last` and `Nodes_append_`.

### Predicate `<LinkedList<T, A>>.own`

Function `LinkedList::new` returns ownership of a `LinkedList` value to the caller. Before we can prove this function's soundness, we must first define what it means to own a `LinkedList` value in separation logic terms. This definition is as follows:

```
pred_ctor elem_fbc<T>(t: thread_id_t)(node: NonNull<Node<T>>) = (*NonNull_ptr(node)).element |-> ?elem &*& <T>.own(t, elem);

pred<T, A> <LinkedList<T, A>>.own(t, ll) =
    Allocator(t, ll.alloc, ?alloc_id) &*&
    Nodes(alloc_id, ll.head, None, ll.tail, None, ?nodes) &*&
    ll.len == length(nodes) &*&
    foreach(nodes, elem_fbc::<T>(t));
```

This definition says that ownership of a `LinkedList` value `ll` by a thread `t` (which is relevant if type T is not `Send`) consists of ownership of the allocator `ll.alloc`, ownership of the linked list of nodes between `ll.head` and `ll.tail` whose length is given by `ll.len`, and ownership of the elements stored in the nodes. To express the latter, it uses the *predicate constructor* `elem_fbc` and the higher-order predicate [`foreach`](https://github.com/verifast/verifast/blob/37bb28bc5edb0e08e5ee8b63a9afd57e7c3b7ffd/bin/rust/list.rsspec#L174).

### `<T>.own` predicates: proof obligations

Since `LinkedList<T, A>` is Send whenever `T` and `A` are Send, VeriFast checks that the proof proves the following lemma:

```
lem LinkedList_send<T, A>(t1: thread_id_t)
    req type_interp::<T>() &*& type_interp::<A>() &*& is_Send(typeid(T)) == true &*& is_Send(typeid(A)) == true &*& LinkedList_own::<T, A>(?t0, ?v);
    ens type_interp::<T>() &*& type_interp::<A>() &*& LinkedList_own::<T, A>(t1, v);
```

In words, this lemma states that if T and A are Send, and `<LinkedList<T, A>>.own(t0, v)` holds, then one can derive `<LinkedList<T, A>>.own(t1, v)` for any thread `t1`. `type_interp::<T>()` expresses that the proof obligations for type T have already been checked, so the proof can call lemma [`Send::send`](https://github.com/verifast/verifast/blob/37bb28bc5edb0e08e5ee8b63a9afd57e7c3b7ffd/bin/rust/rust_belt/general.rsspec#L213):

```
lem LinkedList_elems_send<T>(t0: thread_id_t, t1: thread_id_t)
    req foreach(?nodes, elem_fbc::<T>(t0)) &*& type_interp::<T>() &*& is_Send(typeid(T)) == true;
    ens foreach(nodes, elem_fbc::<T>(t1)) &*& type_interp::<T>();
{
    open foreach(nodes, elem_fbc::<T>(t0));
    match nodes {
        nil => {}
        cons(n, nodes0) => {
            open elem_fbc::<T>(t0)(n);
            Send::send(t0, t1, (*NonNull_ptr(n)).element);
            close elem_fbc::<T>(t1)(n);
            LinkedList_elems_send::<T>(t0, t1);
        }
    }
    close foreach(nodes, elem_fbc::<T>(t1));
}

lem LinkedList_send<T, A>(t1: thread_id_t)
    req type_interp::<T>() &*& type_interp::<A>() &*& is_Send(typeid(T)) == true &*& is_Send(typeid(A)) == true &*& LinkedList_own::<T, A>(?t0, ?v);
    ens type_interp::<T>() &*& type_interp::<A>() &*& LinkedList_own::<T, A>(t1, v);
{
    open <LinkedList<T, A>>.own(t0, v);
    assert Allocator(t0, ?alloc, _);
    std::alloc::Allocator_send(t1, alloc);
    LinkedList_elems_send::<T>(t0, t1);
    close <LinkedList<T, A>>.own(t1, v);
}
```

Furthermore, if a struct S has fields that might need to be dropped, and the struct does not implement Drop, then VeriFast checks that the proof defines a lemma `S_drop` that proves that `<S>.own` implies ownership of the
field values that might need to be dropped. This is the case for Node, so the proof defines the following lemma:

```
lem Node_drop<T>()
    req Node_own::<T>(?_t, ?_v);
    ens <T>.own(_t, _v.element);
{
    open <Node<T>>.own(_t, _v);
}
```

### Function `LinkedList::new`

The proof of `LinkedList::new` is straightforward:

```rust
pub const fn new() -> Self
//@ req thread_token(?t);
//@ ens thread_token(t) &*& <LinkedList<T, Global>>.own(t, result);
//@ on_unwind_ens thread_token(t);
{
    let r = LinkedList { head: None, tail: None, len: 0, alloc: Global, marker: PhantomData };
    //@ close foreach(nil, elem_fbc::<T>(t));
    //@ std::alloc::produce_Allocator_Global(t);
    //@ close <LinkedList<T, Global>>.own(t, r);
    r
}
```

Since this function is not marked as `unsafe`, VeriFast checks that its specification implies semantic well-typedness. Every non-`unsafe` function receives ownership of a `thread_token` for the current thread (which allows it to access non-thread-safe resources owned by the thread). It must also return this token at the end of the call. Furthermore, `new`'s postcondition asserts ownership of the `LinkedList` value returned by the function.

The proof calls lemma [`std::alloc::produce_Allocator_Global`](https://github.com/verifast/verifast/blob/37bb28bc5edb0e08e5ee8b63a9afd57e7c3b7ffd/bin/rust/std/lib.rsspec#L576) to obtain (shared) ownership of the global allocator.

### Function `LinkedList::new_in`

In contrast, function `LinkedList::new_in` requires the caller to provide ownership of the allocator:

```rust
pub const fn new_in(alloc: A) -> Self
//@ req thread_token(?t) &*& <A>.own(t, alloc);
//@ ens thread_token(t) &*& <LinkedList<T, A>>.own(t, result);
//@ on_unwind_ens thread_token(t);
{
    let r = LinkedList { head: None, tail: None, len: 0, alloc, marker: PhantomData };
    //@ std::alloc::open_Allocator_own::<A>(alloc);
    //@ close foreach(nil, elem_fbc::<T>(t));
    //@ close <LinkedList<T, A>>.own(t, r);
    r
}
```

The proof calls lemma [`std::alloc::open_Allocator_own`](https://github.com/verifast/verifast/blob/37bb28bc5edb0e08e5ee8b63a9afd57e7c3b7ffd/bin/rust/std/lib.rsspec#L467) to turn the `<A>.own` chunk into an `Allocator` chunk that specifies the A value's allocator identifier. (We cannot simply use the A value as the allocator identifier since different values may represent the same allocator. For example, if a variable `x` contains an Allocator value, then `x` and `&x` are different values that represent the same allocator.)

### Function `LinkedList::clear`

For function `LinkedList::clear`, the specification is fairly straightforward, but the proof is a bit involved:

```rust
pub fn clear(&mut self)
//@ req thread_token(?t) &*& *self |-> ?self0 &*& <LinkedList<T, A>>.own(t, self0);
//@ ens thread_token(t) &*& *self |-> ?self1 &*& <LinkedList<T, A>>.own(t, self1);
//@ on_unwind_ens thread_token(t) &*& *self |-> ?self1 &*& <LinkedList<T, A>>.own(t, self1);
{
    //@ open_points_to(self);
    //@ open <LinkedList<T, A>>.own(t, self0);
    //@ let alloc_ref = precreate_ref(&(*self).alloc);
    // We need to drop the nodes while keeping self.alloc
    // We can do this by moving (head, tail, len) into a new list that borrows self.alloc
    //@ let k = begin_lifetime();
    {
        //@ let_lft 'a = k;
        //@ std::alloc::init_ref_Allocator_at_lifetime::<'a, A>(alloc_ref);
        let ll = LinkedList {
            head: self.head.take(),
            tail: self.tail.take(),
            len: mem_take_usize__VeriFast_wrapper(&mut self.len),
            alloc: &self.alloc,
            marker: PhantomData,
        };
        //@ close <LinkedList<T, &'a A>>.own(t, ll);
        drop/*@::<LinkedList<T, &'a A>> @*/(ll);
    }
    //@ end_lifetime(k);
    //@ std::alloc::end_ref_Allocator_at_lifetime::<A>();
    //@ close_points_to(self);
    //@ close foreach(nil, elem_fbc::<T>(t));
    //@ close <LinkedList<T, A>>.own(t, *self);
}
```

The `open_points_to` ghost command simply turns the points-to chunk for `self` into a separate chunk for each field of `self` (plus a padding chunk).

Most of the complexity of this proof is due to Rust's rule that mutating memory pointed to by an active shared reference is Undefined Behavior. The code creates a shared reference to `self.alloc`, so VeriFast needs to ensure that field is not mutated while the shared reference is used. It does so by, first of all, interpreting the creation of a shared reference of a place P (e.g. field `self.alloc`) as an operation that yields a place P' that is *different* from P: even though it has the same address, it has different [*provenance*](https://doc.rust-lang.org/std/ptr/index.html#provenance). As a result, points-to chunks for P do not provide access to P'. Secondly, VeriFast requires that, *before* a shared reference to a place P is created, some *fraction* of the ownership of P is transferred from P to the new place P'. (To read from a place, fractional ownership suffices; to write to it, full ownership is required.) To enable this, VeriFast requires the user to *pre-create* the shared reference, using lemma [`precreate_ref`](https://github.com/verifast/verifast/blob/37bb28bc5edb0e08e5ee8b63a9afd57e7c3b7ffd/bin/rust/aliasing.rsspec#L67). This lemma produces permission to *initialize* the new reference, which means transferring fractional ownership of the original place to it.

Fractional ownership of `self.alloc` is passed to `drop`, but `drop` does not return it in its postcondition. To recover full ownership of `self.alloc`, we need to exploit the fact that the shared reference to `self.alloc` is active only for a limited *lifetime*. To do so, we create a lifetime `k` for the shared reference using lemma [`begin_lifetime`](https://github.com/verifast/verifast/blob/37bb28bc5edb0e08e5ee8b63a9afd57e7c3b7ffd/bin/rust/rust_belt/lifetime_logic.rsspec#L67), and then introduce a type-system-level lifetime variable `'a` that denotes it using `let_lft`; this lifetime variable is in scope only until the end of the block in which it is introduced. Afterwards, we can end the lifetime using `end_lifetime`.

Once the lifetime variable is in scope, we can initialize the shared reference using lemma [`std::alloc::init_ref_Allocator_at_lifetime`](https://github.com/verifast/verifast/blob/37bb28bc5edb0e08e5ee8b63a9afd57e7c3b7ffd/bin/rust/std/lib.rsspec#L517). After the lifetime has ended, we can recover full ownership of `self.alloc` using lemma [`std::alloc::end_ref_Allocator_at_lifetime`](https://github.com/verifast/verifast/blob/37bb28bc5edb0e08e5ee8b63a9afd57e7c3b7ffd/bin/rust/std/lib.rsspec#L522).

### Function `LinkedList::pop_front_node`

Now, let's look at the specification for function `LinkedList::pop_front_node`:

```rust
fn pop_front_node<'a>(&'a mut self) -> Option<Box<Node<T>, &'a A>>
//@ req thread_token(?t) &*& [?qa]lifetime_token('a) &*& full_borrow('a, <LinkedList<T, A>>.full_borrow_content(t, self));
//@ ens thread_token(t) &*& [qa]lifetime_token('a) &*& <Option<std::boxed::Box<Node<T>, &'a A>>>.own(t, result);
```

`[?qa]lifetime_token('a)` asserts ownership of a *fraction* `qa` (a real number greater than zero and not greater than one) of the *lifetime token* for lifetime `'a`. 
Every non-`unsafe` function receives such a lifetime token fraction for each of its lifetime parameters. Since ending a lifetime consumes the full lifetime token, a fractional lifetime token proves that the lifetime is alive, without necessarily giving the owner permission to end the lifetime.

Function `pop_front_node` takes a mutable reference to a place storing a `LinkedList` value, just like function `clear` does (see above). The precondition for function `clear` asserts ownership of the place the reference points to, as well ownership of the value stored by the place, as does its postcondition. That is, the function receives ownership of the place and the value from the caller, and returns it back to the caller when it returns. This, however, does not work for function `pop_front_node`: it must return ownership of a Box that holds a reference to the LinkedList's allocator. It cannot also *separately* return full ownership of the LinkedList value, which asserts full ownership of its allocator.
In fact, after a client calls this function, the Rust type system will prevent them from using their LinkedList value until the lifetime `'a` has ended.

To reflect this in separation logic, `pop_front_node` *does not* receive ownership of the place or the LinkedList value. Instead, it receives only a *full borrow* at lifetime `'a` of these resources. `full_borrow(k, p)` asserts that the resources asserted by predicate value `p` have been borrowed under lifetime `k`, and asserts the exclusive permission to temporarily obtain ownership of these resources, provided that `k` has not yet ended. `<T>.full_borrow_content(t, l)` is an expression built into VeriFast that denotes a predicate value that asserts resources `*l |-> ?v &*& <T>.own(t, v)`, i.e. ownership of the place at `l` and the value stored at that place (accessible to thread `t`).

The specification that VeriFast generates to express the soundness of a non-`unsafe` function that takes a mutable reference depends on whether the lifetime of the mutable reference also appears elsewhere in the function's type or not. If it does not, the specification is like that of function `clear` above; otherwise, it is like that of function `pop_front_node`.

Now, let's look at the proof:

```rust
fn pop_front_node<'a>(&'a mut self) -> Option<Box<Node<T>, &'a A>>
//@ req thread_token(?t) &*& [?qa]lifetime_token('a) &*& full_borrow('a, <LinkedList<T, A>>.full_borrow_content(t, self));
//@ ens thread_token(t) &*& [qa]lifetime_token('a) &*& <Option<std::boxed::Box<Node<T>, &'a A>>>.own(t, result);
{
    // This method takes care not to create mutable references to whole nodes,
    // to maintain validity of aliasing pointers into `element`.
    //@ let klong = open_full_borrow_strong('a, <LinkedList<T, A>>.full_borrow_content(t, self), qa);
    //@ open LinkedList_full_borrow_content::<T, A>(t, self)();
    //@ open <LinkedList<T, A>>.own(t, *self);
    //@ assert Nodes(?alloc_id, _, _, _, _, _);
    let r;
    {
        /*@
        pred fbc1() =
            (*self).head |-> ?head_ &*&
            (*self).tail |-> ?tail_ &*&
            Nodes(alloc_id, head_, None, tail_, None, ?nodes) &*&
            (*self).len |-> length(nodes) &*&
            (*self).marker |-> ?_ &*&
            struct_LinkedList_padding(self) &*&
            foreach(nodes, elem_fbc::<T>(t));
        @*/
        //@ close fbc1();
        //@ std::alloc::close_Allocator_full_borrow_content_::<A>(t, &(*self).alloc);
        //@ close sep(fbc1, std::alloc::Allocator_full_borrow_content_::<A>(t, &(*self).alloc, alloc_id))();
        /*@
        {
            pred Ctx() = true;
            produce_lem_ptr_chunk full_borrow_convert_strong(Ctx, sep(fbc1, std::alloc::Allocator_full_borrow_content_::<A>(t, &(*self).alloc, alloc_id)), klong, <LinkedList<T, A>>.full_borrow_content(t, self))() {
                open Ctx();
                open sep(fbc1, std::alloc::Allocator_full_borrow_content_::<A>(t, &(*self).alloc, alloc_id))();
                open fbc1();
                std::alloc::open_Allocator_full_borrow_content_::<A>(t, &(*self).alloc, alloc_id);
                close <LinkedList<T, A>>.own(t, *self);
                close <LinkedList<T, A>>.full_borrow_content(t, self)();
            } {
                close Ctx();
                close_full_borrow_strong(klong, <LinkedList<T, A>>.full_borrow_content(t, self), sep(fbc1, std::alloc::Allocator_full_borrow_content_::<A>(t, &(*self).alloc, alloc_id)));
                full_borrow_mono(klong, 'a, sep(fbc1, std::alloc::Allocator_full_borrow_content_::<A>(t, &(*self).alloc, alloc_id)));
                full_borrow_split('a, fbc1, std::alloc::Allocator_full_borrow_content_::<A>(t, &(*self).alloc, alloc_id));
            }
        }
        @*/
        //@ open_full_borrow(qa/2, 'a, fbc1);
        //@ open fbc1();
        let head = self.head;
        let head_ref = &mut self.head;
        let tail_ref = &mut self.tail;
        let len_ref = &mut self.len;
        //@ std::alloc::share_Allocator_full_borrow_content_('a, t, &(*self).alloc, alloc_id);
        //@ let alloc_ref1 = precreate_ref(&(*self).alloc);
        //@ std::alloc::init_ref_Allocator_share('a, t, alloc_ref1);
        //@ open_frac_borrow('a, ref_initialized_(alloc_ref1), qa/2);
        //@ open [?f]ref_initialized_::<A>(alloc_ref1)();
        let alloc_ref = &self.alloc;
        
        r = match  head {
            None => {
                //@ close [f]ref_initialized_::<A>(alloc_ref)();
                //@ close_frac_borrow(f, ref_initialized_(alloc_ref));
                
                //@ close fbc1();
                //@ close_full_borrow(fbc1);
                //@ close std::option::Option_own::<std::boxed::Box<Node<T>, &'a A>>(t, Option::None);
                //@ leak full_borrow(_, _);
                None
            }
            Some(node) => unsafe {
                //@ std::alloc::close_Allocator_ref::<'a, A>(t, alloc_ref1);
                
                //@ open Nodes(alloc_id, ?head1, None, ?tail1, None, ?nodes1);
                //@ open foreach(nodes1, elem_fbc::<T>(t));
                //@ open elem_fbc::<T>(t)(node);
                let node = Box::from_raw_in(node.as_ptr(), &*alloc_ref);
                //@ close [f]ref_initialized_::<A>(alloc_ref)();
                //@ close_frac_borrow(f, ref_initialized_(alloc_ref));
                //@ std::boxed::Box_separate_contents(&node_1);
                *head_ref = node.next;
                //@ std::boxed::Box_unseparate_contents(&node_1);

                //@ open Nodes(_, ?next, _, ?tail, _, _);
                match *head_ref {
                    None => {
                        *tail_ref = None;
                        //@ close Nodes(alloc_id, next, None, *tail_ref, None, _);
                    }
                    // Not creating new mutable (unique!) references overlapping `element`.
                    Some(head) => {
                        (*head.as_ptr()).prev = None;
                        //@ close Nodes(alloc_id, next, None, (*self).tail, None, _);
                    }
                }

                *len_ref -= 1;
                //@ close fbc1();
                //@ close_full_borrow(fbc1);
                //@ leak full_borrow(_, _);
                //@ let b = node_1;
                //@ assert std::boxed::Box_in(t, b, alloc_id, ?v_node);
                //@ close <Node<T>>.own(t, v_node);
                //@ std::boxed::Box_in_to_own::<Node<T>, &'a A>(node_1);
                //@ close std::option::Option_own::<std::boxed::Box<Node<T>, &'a A>>(t, Option::Some(node_1));
                Some(node)
            }
        };
    }
    r
}
```

To create the box using [`Box::from_raw_in`](https://github.com/verifast/verifast/blob/37bb28bc5edb0e08e5ee8b63a9afd57e7c3b7ffd/bin/rust/std/lib.rsspec#L662), we need an
`Allocator` chunk for the shared reference to `self.alloc`. We obtain it using lemma[`std::alloc::close_Allocator_ref`](https://github.com/verifast/verifast/blob/37bb28bc5edb0e08e5ee8b63a9afd57e7c3b7ffd/bin/rust/std/lib.rsspec#L499). But it requires an `Allocator_share` chunk for the shared reference. That one, we
obtain using lemma [`std::alloc::init_ref_Allocator_share`](https://github.com/verifast/verifast/blob/37bb28bc5edb0e08e5ee8b63a9afd57e7c3b7ffd/bin/rust/std/lib.rsspec#L494)
from an `Allocator_share` chunk for `self.alloc` itself (the original place the shared reference was created from), which in turn we obtain using lemma
[`std::alloc::share_Allocator_full_borrow_content_`](https://github.com/verifast/verifast/blob/37bb28bc5edb0e08e5ee8b63a9afd57e7c3b7ffd/bin/rust/std/lib.rsspec#L481) from
a full borrow of predicate value `std::alloc::Allocator_full_borrow_content_::<A>(t, &(*self).alloc, alloc_id)`.

That full borrow, we obtain by transforming `full_borrow('a, <LinkedList<T, A>>.full_borrow_content(t, self))` into
`full_borrow('a, sep(fbc1, std::alloc::Allocator_full_borrow_content_::<A>(t, &(*self).alloc, alloc_id)))` and then splitting the resulting full borrow using lemma
[`full_borrow_split`](https://github.com/verifast/verifast/blob/37bb28bc5edb0e08e5ee8b63a9afd57e7c3b7ffd/bin/rust/rust_belt/lifetime_logic.rsspec#L213).

To perform this transformation, we call lemma [`open_full_borrow_strong`](https://github.com/verifast/verifast/blob/37bb28bc5edb0e08e5ee8b63a9afd57e7c3b7ffd/bin/rust/rust_belt/lifetime_logic.rsspec#L144) and then lemma [`close_full_borrow_strong`](https://github.com/verifast/verifast/blob/37bb28bc5edb0e08e5ee8b63a9afd57e7c3b7ffd/bin/rust/rust_belt/lifetime_logic.rsspec#L153). The proof does not use the simpler lemma [`open_full_borrow`](https://github.com/verifast/verifast/blob/37bb28bc5edb0e08e5ee8b63a9afd57e7c3b7ffd/bin/rust/rust_belt/lifetime_logic.rsspec#L131), because after opening `full_borrow(k, p)`, the latter requires the original predicate value `p` to be re-established when closing the full borrow back up. Notice that both lemmas for opening a full borrow force the caller to close it back up before the caller returns by capturing a fraction of the lifetime token.

### Predicate `<LinkedList<T, A>>.share`

Function `LinkedList::len` takes a shared reference to a LinkedList object. It should therefore receive *shared ownership* of the object. The precise meaning of "shared ownership of an object of type T at location `l` accessible to thread `t`", written as `<T>.share(k, t, l)`, depends on the type. For LinkedList, the proof defines it as follows:

```
pred Nodes1<T>(alloc_id: any, n: Option<NonNull<Node<T>>>, prev: Option<NonNull<Node<T>>>, last: Option<NonNull<Node<T>>>, next: Option<NonNull<Node<T>>>, nodes: list<NonNull<Node<T>>>; prevs: list<Option<NonNull<Node<T>>>>, nexts: list<Option<NonNull<Node<T>>>>) =
    match nodes {
        nil =>
            n == next &*& last == prev &*& prevs == nil &*& nexts == nil,
        cons(n_, nodes0) =>
            n == Option::Some(n_) &*&
            alloc_block_in(alloc_id, NonNull_ptr(n_) as *u8, Layout::new_::<Node<T>>()) &*& struct_Node_padding(NonNull_ptr(n_)) &*&
            (*NonNull_ptr(n_)).prev |-> prev &*&
            (*NonNull_ptr(n_)).next |-> ?next0 &*&
            pointer_within_limits(&(*NonNull_ptr(n_)).element) == true &*&
            Nodes1(alloc_id, next0, n, last, next, nodes0, ?prevs0, ?nexts0) &*&
            prevs == cons(prev, prevs0) &*&
            nexts == cons(next0, nexts0)
    };

pred_ctor LinkedList_frac_borrow_content<T, A>(alloc_id: any, l: *LinkedList<T, A>, head: Option<NonNull<Node<T>>>, tail: Option<NonNull<Node<T>>>, nodes: list<NonNull<Node<T>>>, prevs: list<Option<NonNull<Node<T>>>>, nexts: list<Option<NonNull<Node<T>>>>)(;) =
    (*l).head |-> head &*& (*l).tail |-> tail &*& Nodes1(alloc_id, head, None, tail, None, nodes, prevs, nexts) &*&
    (*l).len |-> length(nodes) &*& struct_LinkedList_padding(l);

inductive LinkedList_share_info<T> = LinkedList_share_info(alloc_id: any, head: Option<NonNull<Node<T>>>, tail: Option<NonNull<Node<T>>>, nodes: list<NonNull<Node<T>>>, prevs: list<Option<NonNull<Node<T>>>>, nexts: list<Option<NonNull<Node<T>>>>);

pred_ctor elem_share<T>(k: lifetime_t, t: thread_id_t)(node: NonNull<Node<T>>) = [_](<T>.share(k, t, &(*NonNull_ptr(node)).element));

pred<T, A> <LinkedList<T, A>>.share(k, t, l) =
    exists(LinkedList_share_info(?alloc_id, ?head, ?tail, ?nodes, ?prevs, ?nexts)) &*&
    [_]frac_borrow(k, LinkedList_frac_borrow_content::<T, A>(alloc_id, l, head, tail, nodes, prevs, nexts)) &*&
    [_](<A>.share(k, t, &(*l).alloc)) &*&
    [_]foreach(nodes, elem_share::<T>(k, t));
```

`<LinkedList<T, A>>.share` asserts a *dummy fraction* (an arbitrary fraction) of a *fractured borrow* at lifetime `k` of a predicate value `LinkedList_frac_borrow_content::<T, A>(alloc_id, l, head, tail, nodes, prevs, nexts)` asserting ownership of the fields of `l` as well as the nodes between `(*l).head` and `(*l).tail`, as well as shared ownership of the allocator
and the elements. A fractured borrow differs in two ways from a full borrow: firstly, unlike a full borrow, fractional ownership of a fractured borrow suffices for opening it; secondly, opening a fractured borrow produces only a fraction of its contents.

Predicate `Nodes1` is equivalent to predicate `Nodes`, except that `Nodes1`'s `nodes` parameter is an *input parameter*, whereas `Nodes`'s `nodes` parameter is an *output parameter*. This allows `Nodes1` to case-split on `nodes` instead of on whether `n == next`. In turn, this allows us to prove lemma `Nodes1_append`:

```
lem Nodes1_append<T>(head: Option<NonNull<Node<T>>>)
    req [?f]Nodes1::<T>(?alloc_id, head, ?prev, ?n1, ?n2, ?nodes1, ?prevs1, ?nexts1) &*& [f]Nodes1::<T>(alloc_id, n2, n1, ?tail, ?next, ?nodes2, ?prevs2, ?nexts2);
    ens [f]Nodes1::<T>(alloc_id, head, prev, tail, next, append(nodes1, nodes2), append(prevs1, prevs2), append(nexts1, nexts2));
```

A corresponding lemma for `Nodes` (operating on *fractions* of `Nodes` chunks) does *not* hold, because the two segments being appended might overlap.

### `<LinkedList<T, A>>.share` proof obligations

If a proof defines `<T>.share`, it must also define a lemma `T_share_full` that proves that `[_]<T>.share(k, t, l)` can be derived from `full_borrow(k, <T>.full_borrow_content(t, l))`:

```
lem LinkedList_share_full<T, A>(k: lifetime_t, t: thread_id_t, l: *LinkedList<T, A>)
    req type_interp::<T>() &*& type_interp::<A>() &*& atomic_mask(MaskTop) &*& full_borrow(k, LinkedList_full_borrow_content::<T, A>(t, l)) &*& [?q]lifetime_token(k);
    ens type_interp::<T>() &*& type_interp::<A>() &*& atomic_mask(MaskTop) &*& [_]LinkedList_share::<T, A>(k, t, l) &*& [q]lifetime_token(k);
```

Furthermore, it must define a lemma `T_share_mono` that proves that from `[_]<T>.share(k, t, l)` one can derive `[_]<T>.share(k1, t, l)` where lifetime `k1` is included in `k`:

```
lem LinkedList_share_mono<T, A>(k: lifetime_t, k1: lifetime_t, t: thread_id_t, l: *LinkedList<T, A>)
    req type_interp::<T>() &*& type_interp::<A>() &*& lifetime_inclusion(k1, k) == true &*& [_]LinkedList_share::<T, A>(k, t, l);
    ens type_interp::<T>() &*& type_interp::<A>() &*& [_]LinkedList_share::<T, A>(k1, t, l);
```

Furthermore, it must prove a lemma `init_ref_T` that proves that if someone creates a shared reference to a T, they can initialize it:

```
lem init_ref_LinkedList<T, A>(p: *LinkedList<T, A>)
    req type_interp::<T>() &*& type_interp::<A>() &*& atomic_mask(Nlft) &*& ref_init_perm(p, ?x) &*& [_]LinkedList_share::<T, A>(?k, ?t, x) &*& [?q]lifetime_token(k);
    ens type_interp::<T>() &*& type_interp::<A>() &*& atomic_mask(Nlft) &*& [q]lifetime_token(k) &*& [_]LinkedList_share::<T, A>(k, t, p) &*& [_]frac_borrow(k, ref_initialized_(p));
```

Finally, if T is Sync, it must prove a lemma `T_sync` that derives `[_]<T>.share(k, t1, l)` from `[_]<T>.share(k, t0, l)`, for any threads `t0` and `t1`. Since `LinkedList<T, A>` is
sync whenever T and A are Sync, the proof defines the following lemma:

```
lem LinkedList_sync<T, A>(t1: thread_id_t)
    req type_interp::<T>() &*& type_interp::<A>() &*& is_Sync(typeid(T)) == true &*& is_Sync(typeid(A)) == true &*& [_]LinkedList_share::<T, A>(?k, ?t0, ?l);
    ens type_interp::<T>() &*& type_interp::<A>() &*& [_]LinkedList_share::<T, A>(k, t1, l);
```

### Function `LinkedList::len`

The proof of function `LinkedList::len` is as follows:

```rust
pub fn len(&self) -> usize
//@ req [?f](*self).len |-> ?len;
//@ ens [f](*self).len |-> len &*& result == len;
//@ on_unwind_ens false;
/*@
safety_proof {
    assert [?q]lifetime_token(?k);
    open <LinkedList<T, A>>.share(k, _t, self);
    assert [_]exists(LinkedList_share_info(?alloc_id, ?head, ?tail, ?nodes, ?prevs, ?nexts));
    open_frac_borrow(k, LinkedList_frac_borrow_content::<T, A>(alloc_id, self, head, tail, nodes, prevs, nexts), q);
    open [?f]LinkedList_frac_borrow_content::<T, A>(alloc_id, self, head, tail, nodes, prevs, nexts)();
    call();
    close [f]LinkedList_frac_borrow_content::<T, A>(alloc_id, self, head, tail, nodes, prevs, nexts)();
    close_frac_borrow(f, LinkedList_frac_borrow_content::<T, A>(alloc_id, self, head, tail, nodes, prevs, nexts));
}
@*/
{
    self.len
}
```

Function `len` is not marked as `unsafe`, so VeriFast checks that its specification implies its soundness. However, in this case it cannot prove this automatically. Therefore, a `safety_proof` clause is provided that proves this property. VeriFast verifies the body of the `safety_proof` clause as if it was the body of the following lemma:
```
lem len_safe(self: &LinkedList<T, A>) -> usize
    req thread_token(?_t) &*& [?_q]lifetime_token(?_k) &*& [_]<LinkedList<T, A>>.share(_k, _t, self);
    ens thread_token(_t) &*& [_q]lifetime_token(_k);
```
The body of the `safety_proof` clause must call the `len` function exactly once using special syntax `call();`. It simply opens the fractured borrow before the `call()` and
closes it back up afterwards.

## Caveats

First of all, this proof was performed with the following VeriFast command-line flags:
- `-skip_specless_fns`: VeriFast ignores the functions that do not have a `req` or `ens` clause.
- `-ignore_unwind_paths`: This proof ignores code that is reachable only when unwinding.
- `-allow_assume`: This proof uses a number of `assume` ghost statements and `assume_correct` clauses. These must be carefully audited.

Secondly, since VeriFast uses the `rustc` frontend, which assumes a particular target architecture, VeriFast's results hold only for the used Rust toolchain's target architecture. When VeriFast reports "0 errors found" for a Rust program, it always reports the targeted architecture as well (e.g. `0 errors found (2149 statements verified) (target: x86_64-unknown-linux-gnu (LP64))`).

Thirdly, VeriFast has a number of [known unsoundnesses](https://github.com/verifast/verifast/issues?q=is%3Aissue+is%3Aopen+label%3Aunsoundness) (reasons why VeriFast might in some cases incorrectly accept a program), including the following:
- VeriFast does not yet fully verify compliance with Rust's [pointer aliasing rules](https://doc.rust-lang.org/reference/behavior-considered-undefined.html).
- VeriFast does not yet properly verify compliance of custom type interpretations with Rust's [variance](https://doc.rust-lang.org/reference/subtyping.html#variance) rules.
- The current standard library specifications do not [prevent an allocated memory block from outliving its allocator](https://github.com/verifast/verifast/issues/829). This is sound only if the global allocator is used.

Fourthly, unlike foundational tools such as [RefinedRust](https://plv.mpi-sws.org/refinedrust/), VeriFast has not itself been verified, so there are undoubtedly also unknown unsoundnesses. Such unsoundnesses might exist in VeriFast's [symbolic execution engine](https://github.com/model-checking/verify-rust-std/issues/213#issuecomment-2531006855) [itself](https://github.com/model-checking/verify-rust-std/issues/213#issuecomment-2534922580) or in its [prelude](https://github.com/verifast/verifast/tree/master/bin/rust) (definitions and axioms automatically imported at the start of every verification run) or in the [specifications](https://github.com/verifast/verifast/blob/master/bin/rust/std/lib.rsspec) it uses for the Rust standard library functions called by the program being verified.
