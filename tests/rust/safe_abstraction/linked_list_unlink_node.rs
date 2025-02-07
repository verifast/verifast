//! A doubly-linked list with owned nodes.
//!
//! The `LinkedList` allows pushing and popping elements at either end
//! in constant time.
//!
//! NOTE: It is almost always better to use [`Vec`] or [`VecDeque`] because
//! array-based containers are generally faster,
//! more memory efficient, and make better use of CPU cache.
//!
//! [`Vec`]: crate::vec::Vec
//! [`VecDeque`]: super::vec_deque::VecDeque

#![stable(feature = "rust1", since = "1.0.0")]

use core::cmp::Ordering;
use core::hash::{Hash, Hasher};
use core::iter::FusedIterator;
use core::marker::PhantomData;
use core::ptr::NonNull;
use core::{fmt, mem};

use super::SpecExtend;
use crate::alloc::{Allocator, Global};
use crate::boxed::Box;

//@ use std::alloc::{alloc_block_in, Layout, Global, Allocator};
//@ use std::option::{Option, Option::None, Option::Some};
//@ use std::ptr::{NonNull, NonNull_ptr};
//@ use std::boxed::Box_in;

/*@

lem foreach_unappend<a>(xs1: list<a>, xs2: list<a>, p: pred(a))
    req foreach(append(xs1, xs2), p);
    ens foreach(xs1, p) &*& foreach(xs2, p);
{
    match xs1 {
        nil => {}
        cons(x, xs10) => {
            open foreach(_, _);
            foreach_unappend(xs10, xs2, p);
        }
    }
    close foreach(xs1, p);
}


pred foreachp2<a, b>(xs: list<a>, p: pred(a; b); ys: list<b>) =
    match xs {
        nil => ys == nil,
        cons(x, xs0) => p(x, ?y) &*& foreachp2(xs0, p, ?ys0) &*& ys == cons(y, ys0)
    };

lem_auto foreachp2_inv<a, b>()
    req foreachp2::<a, b>(?xs, ?p, ?ys);
    ens foreachp2::<a, b>(xs, p, ys) &*& length(ys) == length(xs);
{
    open foreachp2(xs, p, ys);
    match xs {
        nil => {}
        cons(x, xs0) => {
            foreachp2_inv();
        }
    }
    close foreachp2(xs, p, ys);
}

lem foreachp2_append<a, b>(xs1: list<a>, xs2: list<a>, p: pred(a; b))
    req foreachp2(xs1, p, ?ys1) &*& foreachp2(xs2, p, ?ys2);
    ens foreachp2(append(xs1, xs2), p, append(ys1, ys2));
{
    open foreachp2(xs1, p, ys1);
    match xs1 {
        nil => {}
        cons(x, xs10) => {
            foreachp2_append(xs10, xs2, p);
            close foreachp2(append(xs1, xs2), p, append(ys1, ys2));
        }
    }
}

lem foreachp2_unappend<a, b>(xs1: list<a>, xs2: list<a>, p: pred(a; b))
    req foreachp2(append(xs1, xs2), p, ?ys);
    ens foreachp2(xs1, p, take(length(xs1), ys)) &*& foreachp2(xs2, p, drop(length(xs1), ys));
{
    match xs1 {
        nil => {}
        cons(x, xs10) => {
            open foreachp2(_, _, _);
            foreachp2_unappend(xs10, xs2, p);
        }
    }
    close foreachp2(xs1, p, take(length(xs1), ys));
}

@*/

#[cfg(test)]
mod tests;

/// A doubly-linked list with owned nodes.
///
/// The `LinkedList` allows pushing and popping elements at either end
/// in constant time.
///
/// A `LinkedList` with a known list of items can be initialized from an array:
/// ```
/// use std::collections::LinkedList;
///
/// let list = LinkedList::from([1, 2, 3]);
/// ```
///
/// NOTE: It is almost always better to use [`Vec`] or [`VecDeque`] because
/// array-based containers are generally faster,
/// more memory efficient, and make better use of CPU cache.
///
/// [`Vec`]: crate::vec::Vec
/// [`VecDeque`]: super::vec_deque::VecDeque
#[stable(feature = "rust1", since = "1.0.0")]
#[cfg_attr(not(test), rustc_diagnostic_item = "LinkedList")]
#[rustc_insignificant_dtor]
pub struct LinkedList<
    T,
    #[unstable(feature = "allocator_api", issue = "32838")] A: Allocator = Global,
> {
    head: Option<NonNull<Node<T>>>,
    tail: Option<NonNull<Node<T>>>,
    len: usize,
    alloc: A,
    marker: PhantomData<Box<Node<T>, A>>,
}

struct Node<T> {
    next: Option<NonNull<Node<T>>>,
    prev: Option<NonNull<Node<T>>>,
    element: T,
}

/*@

pred<T> <Node<T>>.own(t, node) = <T>.own(t, node.element);

lem Node_drop<T>()
    req Node_own::<T>(?_t, ?_v);
    ens <T>.own(_t, _v.element);
{
    open <Node<T>>.own(_t, _v);
}

lem Node_own_mono<T0, T1>()
    req type_interp::<T0>() &*& type_interp::<T1>() &*& Node_own::<T0>(?t, ?v) &*& is_subtype_of::<T0, T1>() == true;
    ens type_interp::<T0>() &*& type_interp::<T1>() &*& Node_own::<T1>(t, Node::<T1> { next: upcast(v.next), prev: upcast(v.prev), element: upcast(v.element) });
{
    open <Node<T0>>.own(t, v);
    own_mono::<T0, T1>(t, v.element);
    Node_upcast::<T0, T1>(v);
    close <Node<T1>>.own(t, upcast(v));
}

lem Node_send<T>(t1: thread_id_t)
    req type_interp::<T>() &*& is_Send(typeid(T)) == true &*& Node_own::<T>(?t0, ?v);
    ens type_interp::<T>() &*& Node_own::<T>(t1, v);
{
    open <Node<T>>.own(t0, v);
    Send::send::<T>(t0, t1, v.element);
    close <Node<T>>.own(t1, v);
}

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

lem Nodes_split_off_last<T>(n: Option<NonNull<Node<T>>>)
    req Nodes::<T>(?alloc_id, n, ?prev, ?last, ?next, ?nodes) &*& n != next;
    ens last == Option::Some(?last_) &*&
        Nodes::<T>(alloc_id, n, prev, ?last1, last, ?nodes0) &*&
        alloc_block_in(alloc_id, NonNull_ptr(last_) as *u8, Layout::new_::<Node<T>>()) &*&
        (*NonNull_ptr(last_)).prev |-> last1 &*&
        (*NonNull_ptr(last_)).next |-> next &*&
        pointer_within_limits(&(*NonNull_ptr(last_)).element) == true &*&
        struct_Node_padding(NonNull_ptr(last_)) &*&
        nodes == append(nodes0, [last_]);
{
    open Nodes::<T>(alloc_id, n, prev, last, next, nodes);
    assert Nodes(alloc_id, ?next0, _, _, _, _);
    assert n == Option::Some(?n_);
    if next0 == next {
        open Nodes(alloc_id, next0, _, _, _, _);
        close Nodes::<T>(alloc_id, n, prev, prev, n, []);
    } else {
        Nodes_split_off_last(next0);
        assert Nodes(alloc_id, next0, n, ?last1, last, ?nodes0);
        close Nodes::<T>(alloc_id, n, prev, last1, last, cons(n_, nodes0));
    }
}

lem Nodes_append_one_<T>(head: Option<NonNull<Node<T>>>)
    req Nodes::<T>(?alloc_id, head, ?prev, ?last, Option::Some(?n), ?nodes1) &*&
        alloc_block_in(alloc_id, NonNull_ptr(n) as *u8, Layout::new_::<Node<T>>()) &*&
        (*NonNull_ptr(n)).prev |-> last &*&
        (*NonNull_ptr(n)).next |-> ?next &*&
        pointer_within_limits(&(*NonNull_ptr(n)).element) == true &*&
        struct_Node_padding(NonNull_ptr(n)) &*&
        Nodes(alloc_id, next, Option::Some(n), ?tail, None, ?nodes2);
    ens Nodes(alloc_id, head, prev, Option::Some(n), next, append(nodes1, [n])) &*&
        Nodes(alloc_id, next, Option::Some(n), tail, None, nodes2);
{
    open Nodes::<T>(alloc_id, head, prev, last, Option::Some(n), nodes1);
    if head == Option::Some(n) {
        open Nodes(alloc_id, next, Option::Some(n), tail, None, nodes2);
        close Nodes(alloc_id, next, Option::Some(n), tail, None, nodes2);
        close Nodes(alloc_id, next, Option::Some(n), Some(n), next, []);
    } else {
        open Nodes(alloc_id, next, Option::Some(n), tail, None, nodes2);
        close Nodes(alloc_id, next, Option::Some(n), tail, None, nodes2);
        open Nodes(_, ?next0, head, _, _, _);
        close Nodes(alloc_id, next0, head, last, Option::Some(n), tail(nodes1));
        Nodes_append_one_(next0);
    }
    close Nodes::<T>(alloc_id, head, prev, Some(n), next, append(nodes1, [n]));
}

lem Nodes_append<T>(n: Option<NonNull<Node<T>>>)
    req Nodes::<T>(?alloc_id, n, ?prev, ?n1, ?n2, ?nodes1) &*& Nodes::<T>(alloc_id, n2, n1, ?tail, None, ?nodes2);
    ens Nodes::<T>(alloc_id, n, prev, tail, None, append(nodes1, nodes2));
{
    open Nodes::<T>(alloc_id, n, prev, n1, n2, nodes1);
    if n == n2 {
    } else {
        assert n == Option::Some(?n_);
        Nodes_append((*NonNull_ptr(n_)).next);
        close Nodes::<T>(alloc_id, n, prev, tail, None, append(nodes1, nodes2));
    }
}

lem Nodes_append_<T>(n: Option<NonNull<Node<T>>>)
    req Nodes::<T>(?alloc_id, n, ?prev, ?n1, ?n2, ?nodes1) &*& Nodes::<T>(alloc_id, n2, n1, ?n3, ?n4, ?nodes2) &*& Nodes::<T>(alloc_id, n4, ?n5, ?tail, None, ?nodes3);
    ens Nodes::<T>(alloc_id, n, prev, n3, n4, append(nodes1, nodes2)) &*& Nodes::<T>(alloc_id, n4, n5, tail, None, nodes3);
{
    open Nodes::<T>(alloc_id, n, prev, n1, n2, nodes1);
    if n == n2 {
    } else {
        assert n == Option::Some(?n_);
        Nodes_append_((*NonNull_ptr(n_)).next);
        open Nodes(alloc_id, n4, n5, tail, None, nodes3);
        close Nodes(alloc_id, n4, n5, tail, None, nodes3);
        close Nodes::<T>(alloc_id, n, prev, n3, n4, append(nodes1, nodes2));
    }
}

lem Nodes_append__<T>(n: Option<NonNull<Node<T>>>)
    req Nodes::<T>(?alloc_id, n, ?prev, ?n1, ?n2, ?nodes1) &*& Nodes::<T>(alloc_id, n2, n1, ?n3, Option::Some(?n4), ?nodes2) &*& (*NonNull_ptr(n4)).prev |-> n3;
    ens Nodes::<T>(alloc_id, n, prev, n3, Some(n4), append(nodes1, nodes2)) &*& (*NonNull_ptr(n4)).prev |-> n3;
{
    open Nodes::<T>(alloc_id, n, prev, n1, n2, nodes1);
    if n == n2 {
    } else {
        assert n == Option::Some(?n_);
        Nodes_append__((*NonNull_ptr(n_)).next);
        close Nodes::<T>(alloc_id, n, prev, n3, Some(n4), append(nodes1, nodes2));
    }
}

pred_ctor elem_fbc<T>(t: thread_id_t)(node: NonNull<Node<T>>) = (*NonNull_ptr(node)).element |-> ?elem &*& <T>.own(t, elem);

pred<T, A> <LinkedList<T, A>>.own(t, ll) =
    Allocator(t, ll.alloc, ?alloc_id) &*&
    Nodes(alloc_id, ll.head, None, ll.tail, None, ?nodes) &*&
    ll.len == length(nodes) &*&
    foreach(nodes, elem_fbc::<T>(t));

lem Nodes_upcast<T0, T1>()
    req Nodes::<T0>(?alloc_id, ?head, ?prev, ?tail, ?next, ?nodes) &*& is_subtype_of::<T0, T1>() == true;
    ens Nodes::<T1>(alloc_id, upcast(head), upcast(prev), upcast(tail), upcast(next), upcast(nodes));
{
    assume(false);
}

lem LinkedList_own_mono<T0, T1, A0, A1>()
    req type_interp::<T0>() &*& type_interp::<T1>() &*& type_interp::<A0>() &*& type_interp::<A1>() &*& LinkedList_own::<T0, A0>(?t, ?v) &*& is_subtype_of::<T0, T1>() == true &*& is_subtype_of::<A0, A1>() == true;
    ens type_interp::<T0>() &*& type_interp::<T1>() &*& type_interp::<A0>() &*& type_interp::<A1>() &*& LinkedList_own::<T1, A1>(t, LinkedList::<T1, A1> { head: upcast(v.head), tail: upcast(v.tail), len: upcast(v.len), alloc: upcast(v.alloc), marker: upcast(v.marker) });
{
    open <LinkedList<T0, A0>>.own(t, v);
    LinkedList_upcast::<T0, T1, A0, A1>(v);
    assert Allocator(t, ?alloc, _);
    std::alloc::Allocator_upcast::<A0, A1>(alloc);
    
    assume(false);
    
    //close <LinkedList<T1, A1>>.own(t, upcast(v));
}

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

lem_auto Nodes1_inv<T>()
    req [?f]Nodes1::<T>(?alloc_id, ?head, ?prev, ?last, ?next, ?nodes, ?prevs, ?nexts);
    ens [f]Nodes1::<T>(alloc_id, head, prev, last, next, nodes, prevs, nexts) &*& length(prevs) == length(nodes) &*& length(nexts) == length(nodes);
{
    open [f]Nodes1::<T>(alloc_id, head, prev, last, next, nodes, prevs, nexts);
    match nodes {
        nil => {}
        cons(n, nodes0) => {
            Nodes1_inv::<T>();
        }
    }
    close [f]Nodes1::<T>(alloc_id, head, prev, last, next, nodes, prevs, nexts);
}

lem Nodes1_append<T>(head: Option<NonNull<Node<T>>>)
    req [?f]Nodes1::<T>(?alloc_id, head, ?prev, ?n1, ?n2, ?nodes1, ?prevs1, ?nexts1) &*& [f]Nodes1::<T>(alloc_id, n2, n1, ?tail, ?next, ?nodes2, ?prevs2, ?nexts2);
    ens [f]Nodes1::<T>(alloc_id, head, prev, tail, next, append(nodes1, nodes2), append(prevs1, prevs2), append(nexts1, nexts2));
{
    open Nodes1::<T>(alloc_id, head, prev, n1, n2, nodes1, prevs1, nexts1);
    match nodes1 {
        nil => {}
        cons(n, nodes10) => {
            Nodes1_append::<T>((*NonNull_ptr(n)).next);
            close [f]Nodes1::<T>(alloc_id, head, prev, tail, next, append(nodes1, nodes2), append(prevs1, prevs2), append(nexts1, nexts2));
        }
    }
}

lem Nodes1_split<T>(
        nodes1: list<NonNull<Node<T>>>,
        nodes2: list<NonNull<Node<T>>>,
        prevs1: list<Option<NonNull<Node<T>>>>,
        prevs2: list<Option<NonNull<Node<T>>>>,
        nexts1: list<Option<NonNull<Node<T>>>>,
        nexts2: list<Option<NonNull<Node<T>>>>)
    req [?f]Nodes1::<T>(?alloc_id, ?head, ?prev, ?tail, ?next, append(nodes1, nodes2), append(prevs1, prevs2), append(nexts1, nexts2)) &*& length(prevs1) == length(nodes1) &*& length(nexts1) == length(nodes1);
    ens [f]Nodes1::<T>(alloc_id, head, prev, ?n2, ?n1, nodes1, prevs1, nexts1) &*& [f]Nodes1::<T>(alloc_id, n1, n2, tail, next, nodes2, prevs2, nexts2);
{
    match nodes1 {
        nil => {
            match prevs1 { nil => {} cons(h, t) => {} }
            match nexts1 { nil => {} cons(h, t) => {} }
            open [f]Nodes1::<T>(alloc_id, head, prev, tail, next, append(nodes1, nodes2), append(prevs1, prevs2), append(nexts1, nexts2));
            close [f]Nodes1::<T>(alloc_id, head, prev, tail, next, nodes2, prevs2, nexts2);
            close [f]Nodes1::<T>(alloc_id, head, prev, prev, head, nil, nil, nil);
        }
        cons(n, nodes10) => {
            match prevs1 { nil => {} cons(h, t) => {} }
            match nexts1 { nil => {} cons(h, t) => {} }
            open [f]Nodes1::<T>(alloc_id, head, prev, tail, next, append(nodes1, nodes2), append(prevs1, prevs2), append(nexts1, nexts2));
            Nodes1_split(nodes10, nodes2, tail(prevs1), prevs2, tail(nexts1), nexts2);
            assert [f]Nodes1::<T>(alloc_id, _, _, ?n2, ?n1, nodes10, tail(prevs1), tail(nexts1));
            close [f]Nodes1::<T>(alloc_id, head, prev, n2, n1, nodes1, prevs1, nexts1);
        }
    }
}

lem Nodes_to_Nodes1<T>()
    req Nodes::<T>(?alloc_id, ?n, ?prev, ?last, ?next, ?nodes);
    ens Nodes1::<T>(alloc_id, n, prev, last, next, nodes, _, _);
{
    open Nodes::<T>(alloc_id, n, prev, last, next, nodes);
    if n == next {
    } else {
        Nodes_to_Nodes1::<T>();
    }
    close Nodes1::<T>(alloc_id, n, prev, last, next, nodes, _, _);
}

lem Nodes1_to_Nodes<T>()
    req Nodes1::<T>(?alloc_id, ?n, ?prev, ?last, None, ?nodes, _, _);
    ens Nodes::<T>(alloc_id, n, prev, last, None, nodes);
{
    open Nodes1::<T>(alloc_id, n, prev, last, None, nodes, _, _);
    match nodes {
        nil => {}
        cons(n_, nodes0) => {
            Nodes1_to_Nodes::<T>();
        }
    }
    close Nodes::<T>(alloc_id, n, prev, last, None, nodes);
}

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

fix elem_fbcs<T>(t: thread_id_t, nodes: list<NonNull<Node<T>>>) -> pred() {
    match nodes {
        nil => True,
        cons(n, nodes0) => sep(<T>.full_borrow_content(t, &(*NonNull_ptr(n)).element), elem_fbcs(t, nodes0))
    }
}

lem LinkedList_share_full<T, A>(k: lifetime_t, t: thread_id_t, l: *LinkedList<T, A>)
    req type_interp::<T>() &*& type_interp::<A>() &*& atomic_mask(MaskTop) &*& full_borrow(k, LinkedList_full_borrow_content::<T, A>(t, l)) &*& [?q]lifetime_token(k);
    ens type_interp::<T>() &*& type_interp::<A>() &*& atomic_mask(MaskTop) &*& [_]LinkedList_share::<T, A>(k, t, l) &*& [q]lifetime_token(k);
{
    let klong = open_full_borrow_strong_m(k, LinkedList_full_borrow_content::<T, A>(t, l), q);
    open LinkedList_full_borrow_content::<T, A>(t, l)();
    open <LinkedList<T, A>>.own(t, ?self_);
    assert Nodes(?alloc_id, ?head, None, ?tail, None, ?nodes);
    Nodes_to_Nodes1::<T>();
    assert Nodes1(alloc_id, head, None, tail, None, nodes, ?prevs, ?nexts);
    close LinkedList_frac_borrow_content::<T, A>(alloc_id, l, head, tail, nodes, prevs, nexts)();
    {
        lem iter(nodes_left: list<NonNull<Node<T>>>)
            req foreach(nodes_left, elem_fbc::<T>(t));
            ens elem_fbcs::<T>(t, nodes_left)();
        {
            open foreach(nodes_left, elem_fbc::<T>(t));
            match nodes_left {
                nil => {
                    close True();
                }
                cons(n, nodes_left0) => {
                    iter(nodes_left0);
                    open elem_fbc::<T>(t)(n);
                    close_full_borrow_content::<T>(t, &(*NonNull_ptr(n)).element);
                    close sep(<T>.full_borrow_content(t, &(*NonNull_ptr(n)).element), elem_fbcs(t, nodes_left0))();
                    assert sep(<T>.full_borrow_content(t, &(*NonNull_ptr(n)).element), elem_fbcs(t, nodes_left0)) == elem_fbcs::<T>(t, nodes_left);
                }
            }
        }
        iter(nodes);
    }
    close sep(LinkedList_frac_borrow_content::<T, A>(alloc_id, l, head, tail, nodes, prevs, nexts), elem_fbcs::<T>(t, nodes))();
    std::alloc::close_Allocator_full_borrow_content_::<A>(t, &(*l).alloc);
    {
        pred Ctx() = (*l).marker |-> ?_;
        close sep(std::alloc::Allocator_full_borrow_content_::<A>(t, &(*l).alloc, alloc_id), sep(LinkedList_frac_borrow_content::<T, A>(alloc_id, l, head, tail, nodes, prevs, nexts), elem_fbcs::<T>(t, nodes)))();
        produce_lem_ptr_chunk full_borrow_convert_strong(Ctx, sep(std::alloc::Allocator_full_borrow_content_::<A>(t, &(*l).alloc, alloc_id), sep(LinkedList_frac_borrow_content::<T, A>(alloc_id, l, head, tail, nodes, prevs, nexts), elem_fbcs::<T>(t, nodes))), klong, LinkedList_full_borrow_content::<T, A>(t, l))() {
            open Ctx();
            open sep(std::alloc::Allocator_full_borrow_content_::<A>(t, &(*l).alloc, alloc_id), sep(LinkedList_frac_borrow_content::<T, A>(alloc_id, l, head, tail, nodes, prevs, nexts), elem_fbcs::<T>(t, nodes)))();
            open sep(LinkedList_frac_borrow_content::<T, A>(alloc_id, l, head, tail, nodes, prevs, nexts), elem_fbcs::<T>(t, nodes))();
            open LinkedList_frac_borrow_content::<T, A>(alloc_id, l, head, tail, nodes, prevs, nexts)();
            {
                lem iter(nodes_left: list<NonNull<Node<T>>>)
                    req elem_fbcs::<T>(t, nodes_left)();
                    ens foreach(nodes_left, elem_fbc::<T>(t));
                {
                    match nodes_left {
                        nil => { open True(); }
                        cons(n, nodes_left0) => {
                            open sep(<T>.full_borrow_content(t, &(*NonNull_ptr(n)).element), elem_fbcs::<T>(t, nodes_left0))();
                            iter(nodes_left0);
                            open_full_borrow_content::<T>(t, &(*NonNull_ptr(n)).element);
                            close elem_fbc::<T>(t)(n);
                        }
                    }
                    close foreach(nodes_left, elem_fbc::<T>(t));
                }
                iter(nodes);
            }
            Nodes1_to_Nodes::<T>();
            std::alloc::open_Allocator_full_borrow_content_::<A>(t, &(*l).alloc, alloc_id);
            
            close <LinkedList<T, A>>.own(t, *l);
            close LinkedList_full_borrow_content::<T, A>(t, l)();
        } {
            close Ctx();
            close_full_borrow_strong_m(klong, LinkedList_full_borrow_content::<T, A>(t, l), sep(std::alloc::Allocator_full_borrow_content_::<A>(t, &(*l).alloc, alloc_id), sep(LinkedList_frac_borrow_content::<T, A>(alloc_id, l, head, tail, nodes, prevs, nexts), elem_fbcs::<T>(t, nodes))));
        }
    }
    full_borrow_mono(klong, k, sep(std::alloc::Allocator_full_borrow_content_::<A>(t, &(*l).alloc, alloc_id), sep(LinkedList_frac_borrow_content::<T, A>(alloc_id, l, head, tail, nodes, prevs, nexts), elem_fbcs::<T>(t, nodes))));
    full_borrow_split_m(k, std::alloc::Allocator_full_borrow_content_::<A>(t, &(*l).alloc, alloc_id), sep(LinkedList_frac_borrow_content::<T, A>(alloc_id, l, head, tail, nodes, prevs, nexts), elem_fbcs::<T>(t, nodes)));
    full_borrow_split_m(k, LinkedList_frac_borrow_content::<T, A>(alloc_id, l, head, tail, nodes, prevs, nexts), elem_fbcs::<T>(t, nodes));
    full_borrow_into_frac_m(k, LinkedList_frac_borrow_content::<T, A>(alloc_id, l, head, tail, nodes, prevs, nexts));
    {
        lem iter(nodes_left: list<NonNull<Node<T>>>)
            req type_interp::<T>() &*& atomic_mask(MaskTop) &*& [q]lifetime_token(k) &*& full_borrow(k, elem_fbcs::<T>(t, nodes_left));
            ens type_interp::<T>() &*& atomic_mask(MaskTop) &*& [q]lifetime_token(k) &*& foreach(nodes_left, elem_share::<T>(k, t));
        {
            match nodes_left {
                nil => {
                    leak full_borrow(_, _);
                    close foreach(nodes_left, elem_share::<T>(k, t));
                }
                cons(n, nodes_left0) => {
                    full_borrow_split_m(k, <T>.full_borrow_content(t, &(*NonNull_ptr(n)).element), elem_fbcs::<T>(t, nodes_left0));
                    share_full_borrow_m::<T>(k, t, &(*NonNull_ptr(n)).element);
                    iter(nodes_left0);
                    close elem_share::<T>(k, t)(n);
                    close foreach(nodes_left, elem_share::<T>(k, t));
                }
            }
        }
        iter(nodes);
    }
    close exists(LinkedList_share_info(alloc_id, head, tail, nodes, prevs, nexts));
    std::alloc::share_Allocator_full_borrow_content_::<A>(k, t, &(*l).alloc, alloc_id);
    leak foreach(nodes, _);
    close <LinkedList<T, A>>.share()(k, t, l);
    leak <LinkedList<T, A>>.share(k, t, l);
}

lem LinkedList_share_mono<T, A>(k: lifetime_t, k1: lifetime_t, t: thread_id_t, l: *LinkedList<T, A>)
    req type_interp::<T>() &*& type_interp::<A>() &*& lifetime_inclusion(k1, k) == true &*& [_]LinkedList_share::<T, A>(k, t, l);
    ens type_interp::<T>() &*& type_interp::<A>() &*& [_]LinkedList_share::<T, A>(k1, t, l);
{
    open <LinkedList<T, A>>.share(k, t, l);
    assert [_]exists(LinkedList_share_info(?alloc_id, ?head, ?tail, ?nodes, ?prevs, ?nexts));
    close exists(LinkedList_share_info(alloc_id, head, tail, nodes, prevs, nexts));
    frac_borrow_mono(k, k1, LinkedList_frac_borrow_content::<T, A>(alloc_id, l, head, tail, nodes, prevs, nexts));
    {
        lem iter()
            req [_]foreach(?nodes1, elem_share::<T>(k, t)) &*& type_interp::<T>();
            ens foreach(nodes1, elem_share::<T>(k1, t)) &*& type_interp::<T>();
        {
            open foreach(nodes1, elem_share::<T>(k, t));
            match nodes1 {
                nil => {
                    open foreach(nil, _);
                }
                cons(n, nodes0) => {
                    open elem_share::<T>(k, t)(n);
                    share_mono::<T>(k, k1, t, &(*NonNull_ptr(n)).element);
                    close elem_share::<T>(k1, t)(n);
                    iter();
                }
            }
            close foreach(nodes1, elem_share::<T>(k1, t));
        }
        iter();
    }
    share_mono::<A>(k, k1, t, &(*l).alloc);
    leak foreach(nodes, _);
    close <LinkedList<T, A>>.share(k1, t, l);
    leak <LinkedList<T, A>>.share(k1, t, l);
}

pred ref_end_token_Option_NonNull<T>(p: *Option<NonNull<T>>, x: *Option<NonNull<T>>, f: real, v: Option<NonNull<T>>) =
    [f/2](*x |-> v) &*& ref_end_token(p, x, f/2) &*& (if v != Option::None { ref_end_token(std::option::Option_Some_0_ptr(p), std::option::Option_Some_0_ptr(x), f/2) } else { true });

lem init_ref_Option_NonNull<T>(p: *Option<NonNull<T>>)
    req ref_init_perm(p, ?x) &*& [?f](*x |-> ?v);
    ens [f/2](*p |-> v) &*& ref_initialized(p) &*& ref_end_token_Option_NonNull(p, x, f, v);
{
    match v {
        Option::None => {
            std::option::init_ref_Option_None(p, 1/2);
        }
        Option::Some(v0) => {
            std::option::open_points_to_Option_Some(x);
            std::option::open_ref_init_perm_Option_Some(p);
            std::ptr::init_ref_NonNull(std::option::Option_Some_0_ptr(p), 1/2);
            std::option::init_ref_Option_Some(p, 1/2);
            std::option::close_points_to_Option_Some(p);
            std::option::close_points_to_Option_Some(x);
        }
    }
    close ref_end_token_Option_NonNull(p, x, f, v);
}

lem end_ref_Option_NonNull<T>(p: *Option<NonNull<T>>)
    req ref_initialized(p) &*& ref_end_token_Option_NonNull(p, ?x, ?f, ?v) &*& [f/2](*p |-> v);
    ens [f](*x |-> v);
{
    open ref_end_token_Option_NonNull(p, x, f, v);
    match v {
        Option::None => {
            std::option::end_ref_Option_None(p);
        }
        Option::Some(v0) => {
            std::option::open_points_to_Option_Some(p);
            std::option::end_ref_Option_Some(p);
            std::ptr::end_ref_NonNull(std::option::Option_Some_0_ptr(p));
            std::option::close_points_to_Option_Some(x);
        }
    }
}

lem init_ref_LinkedList<T, A>(p: *LinkedList<T, A>)
    req type_interp::<T>() &*& type_interp::<A>() &*& atomic_mask(Nlft) &*& ref_init_perm(p, ?x) &*& [_]LinkedList_share::<T, A>(?k, ?t, x) &*& [?q]lifetime_token(k);
    ens type_interp::<T>() &*& type_interp::<A>() &*& atomic_mask(Nlft) &*& [q]lifetime_token(k) &*& [_]LinkedList_share::<T, A>(k, t, p) &*& [_]frac_borrow(k, ref_initialized_(p));
{
    open <LinkedList<T, A>>.share(k, t, x);
    assert [_]exists(LinkedList_share_info(?alloc_id, ?head, ?tail, ?nodes, ?prevs, ?nexts));
    close exists(LinkedList_share_info(alloc_id, head, tail, nodes, prevs, nexts));
    open_ref_init_perm_LinkedList(p);
    leak ref_init_perm(&(*p).marker, _);
    
    {
        pred R(;) = ref_initialized(&(*p).head) &*& ref_initialized(&(*p).tail) &*& ref_initialized(&(*p).len) &*& ref_padding_initialized(p);
        {
            let klong = open_frac_borrow_strong_m(k, LinkedList_frac_borrow_content::<T, A>(alloc_id, x, head, tail, nodes, prevs, nexts), q);
            open [?f]LinkedList_frac_borrow_content::<T, A>(alloc_id, x, head, tail, nodes, prevs, nexts)();
            init_ref_Option_NonNull(&(*p).head);
            init_ref_Option_NonNull(&(*p).tail);
            init_ref_padding_LinkedList(p, 1/2);
            std::num::init_ref_usize(&(*p).len, 1/2);
            close [f/2]LinkedList_frac_borrow_content::<T, A>(alloc_id, p, head, tail, nodes, prevs, nexts)();           
            close scaledp(f/2, LinkedList_frac_borrow_content::<T, A>(alloc_id, p, head, tail, nodes, prevs, nexts))();
            close R();
            {
                pred Ctx() =
                    ref_end_token_Option_NonNull(&(*p).head, &(*x).head, f, head) &*&
                    ref_end_token_Option_NonNull(&(*p).tail, &(*x).tail, f, tail) &*&
                    [f/2]Nodes1(alloc_id, head, None, tail, None, nodes, prevs, nexts) &*&
                    [f/2](*x).len |-> length(nodes) &*& ref_end_token(&(*p).len, &(*x).len, f/2) &*&
                    [f/2]struct_LinkedList_padding(x) &*& ref_padding_end_token(p, x, f/2);
                close Ctx();
                close sep(scaledp(f/2, LinkedList_frac_borrow_content::<T, A>(alloc_id, p, head, tail, nodes, prevs, nexts)), R)();
                produce_lem_ptr_chunk frac_borrow_convert_strong(Ctx, sep(scaledp(f/2, LinkedList_frac_borrow_content::<T, A>(alloc_id, p, head, tail, nodes, prevs, nexts)), R), klong, f, LinkedList_frac_borrow_content::<T, A>(alloc_id, x, head, tail, nodes, prevs, nexts))() {
                    open Ctx();
                    open sep(scaledp(f/2, LinkedList_frac_borrow_content::<T, A>(alloc_id, p, head, tail, nodes, prevs, nexts)), R)();
                    open scaledp(f/2, LinkedList_frac_borrow_content::<T, A>(alloc_id, p, head, tail, nodes, prevs, nexts))();
                    open [f/2]LinkedList_frac_borrow_content::<T, A>(alloc_id, p, head, tail, nodes, prevs, nexts)();
                    open R();
                    end_ref_Option_NonNull(&(*p).head);
                    end_ref_Option_NonNull(&(*p).tail);
                    std::num::end_ref_usize(&(*p).len);
                    end_ref_padding_LinkedList(p);
                    close [f]LinkedList_frac_borrow_content::<T, A>(alloc_id, x, head, tail, nodes, prevs, nexts)();
                } {
                    close_frac_borrow_strong_m();
                    full_borrow_mono(klong, k, sep(scaledp(f/2, LinkedList_frac_borrow_content::<T, A>(alloc_id, p, head, tail, nodes, prevs, nexts)), R));
                    full_borrow_split_m(k, scaledp(f/2, LinkedList_frac_borrow_content::<T, A>(alloc_id, p, head, tail, nodes, prevs, nexts)), R);
                    full_borrow_into_frac_m(k, scaledp(f/2, LinkedList_frac_borrow_content::<T, A>(alloc_id, p, head, tail, nodes, prevs, nexts)));
                    frac_borrow_implies_scaled(k, f/2, LinkedList_frac_borrow_content::<T, A>(alloc_id, p, head, tail, nodes, prevs, nexts));
                    full_borrow_into_frac_m(k, R);
                }
            }
        }
    
        init_ref_share_m::<A>(k, t, &(*p).alloc);
        close <LinkedList<T, A>>.share(k, t, p);
        leak <LinkedList<T, A>>.share(k, t, p);
        
        frac_borrow_sep(k, ref_initialized_(&(*p).alloc), R);
        produce_lem_ptr_chunk implies_frac(sep_(ref_initialized_(&(*p).alloc), R), ref_initialized_(p))() {
            open [?f]sep_(ref_initialized_(&(*p).alloc), R)();
            open [f]ref_initialized_::<A>(&(*p).alloc)();
            open [f]R();
            std::marker::close_ref_initialized_PhantomData(&(*p).marker, f);
            close_ref_initialized_LinkedList(p);
            close [f]ref_initialized_::<LinkedList<T, A>>(p)();
        } {
            produce_lem_ptr_chunk implies_frac(ref_initialized_(p), sep_(ref_initialized_(&(*p).alloc), R))() {
                open [?f]ref_initialized_::<LinkedList<T, A>>(p)();
                open_ref_initialized_LinkedList(p);
                close [f]ref_initialized_::<A>(&(*p).alloc)();
                close [f]R();
                close [f]sep_(ref_initialized_(&(*p).alloc), R)();
                leak [f]ref_initialized(&(*p).marker);
            } {
                frac_borrow_implies(k, sep_(ref_initialized_(&(*p).alloc), R), ref_initialized_(p));
            }
        }
    }
}

lem LinkedList_sync<T, A>(t1: thread_id_t)
    req type_interp::<T>() &*& type_interp::<A>() &*& is_Sync(typeid(T)) == true &*& is_Sync(typeid(A)) == true &*& [_]LinkedList_share::<T, A>(?k, ?t0, ?l);
    ens type_interp::<T>() &*& type_interp::<A>() &*& [_]LinkedList_share::<T, A>(k, t1, l);
{
    open <LinkedList<T, A>>.share(k, t0, l);
    assert [_]exists(LinkedList_share_info(?alloc_id, ?head, ?tail, ?nodes_, ?prevs, ?nexts));
    close exists(LinkedList_share_info(alloc_id, head, tail, nodes_, prevs, nexts));
    {
        lem iter()
            req [_]foreach(?nodes, elem_share::<T>(k, t0)) &*& type_interp::<T>();
            ens foreach(nodes, elem_share::<T>(k, t1)) &*& type_interp::<T>();
        {
            open foreach(nodes, elem_share::<T>(k, t0));
            match nodes {
                nil => {}
                cons(n, nodes0) => {
                    open elem_share::<T>(k, t0)(n);
                    Sync::sync::<T>(k, t0, t1, &(*NonNull_ptr(n)).element);
                    close elem_share::<T>(k, t1)(n);
                    iter();
                }
            }
            close foreach(nodes, elem_share::<T>(k, t1));
        }
        iter();
    }
    Sync::sync::<A>(k, t0, t1, &(*l).alloc);
    leak foreach(_, _);
    close <LinkedList<T, A>>.share(k, t1, l);
    leak <LinkedList<T, A>>.share(k, t1, l);
}

@*/

/// An iterator over the elements of a `LinkedList`.
///
/// This `struct` is created by [`LinkedList::iter()`]. See its
/// documentation for more.
#[must_use = "iterators are lazy and do nothing unless consumed"]
#[stable(feature = "rust1", since = "1.0.0")]
pub struct Iter<'a, T: 'a> {
    head: Option<NonNull<Node<T>>>,
    tail: Option<NonNull<Node<T>>>,
    len: usize,
    marker: PhantomData<&'a Node<T>>,
}

#[stable(feature = "collection_debug", since = "1.17.0")]
impl<T: fmt::Debug> fmt::Debug for Iter<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("Iter")
            .field(&*mem::ManuallyDrop::new(LinkedList {
                head: self.head,
                tail: self.tail,
                len: self.len,
                alloc: Global,
                marker: PhantomData,
            }))
            .field(&self.len)
            .finish()
    }
}

// FIXME(#26925) Remove in favor of `#[derive(Clone)]`
#[stable(feature = "rust1", since = "1.0.0")]
impl<T> Clone for Iter<'_, T> {
    fn clone(&self) -> Self {
        Iter { ..*self }
    }
}

/// A mutable iterator over the elements of a `LinkedList`.
///
/// This `struct` is created by [`LinkedList::iter_mut()`]. See its
/// documentation for more.
#[must_use = "iterators are lazy and do nothing unless consumed"]
#[stable(feature = "rust1", since = "1.0.0")]
pub struct IterMut<'a, T: 'a> {
    head: Option<NonNull<Node<T>>>,
    tail: Option<NonNull<Node<T>>>,
    len: usize,
    marker: PhantomData<&'a mut Node<T>>,
}

#[stable(feature = "collection_debug", since = "1.17.0")]
impl<T: fmt::Debug> fmt::Debug for IterMut<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("IterMut")
            .field(&*mem::ManuallyDrop::new(LinkedList {
                head: self.head,
                tail: self.tail,
                len: self.len,
                alloc: Global,
                marker: PhantomData,
            }))
            .field(&self.len)
            .finish()
    }
}

/// An owning iterator over the elements of a `LinkedList`.
///
/// This `struct` is created by the [`into_iter`] method on [`LinkedList`]
/// (provided by the [`IntoIterator`] trait). See its documentation for more.
///
/// [`into_iter`]: LinkedList::into_iter
#[derive(Clone)]
#[stable(feature = "rust1", since = "1.0.0")]
pub struct IntoIter<
    T,
    #[unstable(feature = "allocator_api", issue = "32838")] A: Allocator = Global,
> {
    list: LinkedList<T, A>,
}

#[stable(feature = "collection_debug", since = "1.17.0")]
impl<T: fmt::Debug, A: Allocator> fmt::Debug for IntoIter<T, A> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("IntoIter").field(&self.list).finish()
    }
}

impl<T> Node<T> {
    fn new(element: T) -> Self {
        Node { next: None, prev: None, element }
    }

    fn into_element<A: Allocator>(self: Box<Self, A>) -> T {
        self.element
    }
}

// private methods
impl<T, A: Allocator> LinkedList<T, A> {
    /// Adds the given node to the front of the list.
    ///
    /// # Safety
    /// `node` must point to a valid node that was boxed and leaked using the list's allocator.
    /// This method takes ownership of the node, so the pointer should not be used again.
    #[inline]
    unsafe fn push_front_node(&mut self, node: NonNull<Node<T>>) {
        // This method takes care not to create mutable references to whole nodes,
        // to maintain validity of aliasing pointers into `element`.
        unsafe {
            (*node.as_ptr()).next = self.head;
            (*node.as_ptr()).prev = None;
            let node = Some(node);

            match self.head {
                None => self.tail = node,
                // Not creating new mutable (unique!) references overlapping `element`.
                Some(head) => (*head.as_ptr()).prev = node,
            }

            self.head = node;
            self.len += 1;
        }
    }

    /// Removes and returns the node at the front of the list.
    #[inline]
    fn pop_front_node(&mut self) -> Option<Box<Node<T>, &A>> {
        // This method takes care not to create mutable references to whole nodes,
        // to maintain validity of aliasing pointers into `element`.
        self.head.map(|node| unsafe {
            let node = Box::from_raw_in(node.as_ptr(), &self.alloc);
            self.head = node.next;

            match self.head {
                None => self.tail = None,
                // Not creating new mutable (unique!) references overlapping `element`.
                Some(head) => (*head.as_ptr()).prev = None,
            }

            self.len -= 1;
            node
        })
    }

    /// Adds the given node to the back of the list.
    ///
    /// # Safety
    /// `node` must point to a valid node that was boxed and leaked using the list's allocator.
    /// This method takes ownership of the node, so the pointer should not be used again.
    #[inline]
    unsafe fn push_back_node(&mut self, node: NonNull<Node<T>>) {
        // This method takes care not to create mutable references to whole nodes,
        // to maintain validity of aliasing pointers into `element`.
        unsafe {
            (*node.as_ptr()).next = None;
            (*node.as_ptr()).prev = self.tail;
            let node = Some(node);

            match self.tail {
                None => self.head = node,
                // Not creating new mutable (unique!) references overlapping `element`.
                Some(tail) => (*tail.as_ptr()).next = node,
            }

            self.tail = node;
            self.len += 1;
        }
    }

    /// Removes and returns the node at the back of the list.
    #[inline]
    fn pop_back_node(&mut self) -> Option<Box<Node<T>, &A>> {
        // This method takes care not to create mutable references to whole nodes,
        // to maintain validity of aliasing pointers into `element`.
        self.tail.map(|node| unsafe {
            let node = Box::from_raw_in(node.as_ptr(), &self.alloc);
            self.tail = node.prev;

            match self.tail {
                None => self.head = None,
                // Not creating new mutable (unique!) references overlapping `element`.
                Some(tail) => (*tail.as_ptr()).next = None,
            }

            self.len -= 1;
            node
        })
    }

    /// Unlinks the specified node from the current list.
    ///
    /// Warning: this will not check that the provided node belongs to the current list.
    ///
    /// This method takes care not to create mutable references to `element`, to
    /// maintain validity of aliasing pointers.
    #[inline]
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

    /// Splices a series of nodes between two existing nodes.
    ///
    /// Warning: this will not check that the provided node belongs to the two existing lists.
    #[inline]
    unsafe fn splice_nodes(
        &mut self,
        existing_prev: Option<NonNull<Node<T>>>,
        existing_next: Option<NonNull<Node<T>>>,
        mut splice_start: NonNull<Node<T>>,
        mut splice_end: NonNull<Node<T>>,
        splice_length: usize,
    ) {
        // This method takes care not to create multiple mutable references to whole nodes at the same time,
        // to maintain validity of aliasing pointers into `element`.
        if let Some(mut existing_prev) = existing_prev {
            unsafe {
                existing_prev.as_mut().next = Some(splice_start);
            }
        } else {
            self.head = Some(splice_start);
        }
        if let Some(mut existing_next) = existing_next {
            unsafe {
                existing_next.as_mut().prev = Some(splice_end);
            }
        } else {
            self.tail = Some(splice_end);
        }
        unsafe {
            splice_start.as_mut().prev = existing_prev;
            splice_end.as_mut().next = existing_next;
        }

        self.len += splice_length;
    }

    /// Detaches all nodes from a linked list as a series of nodes.
    #[inline]
    fn detach_all_nodes(mut self) -> Option<(NonNull<Node<T>>, NonNull<Node<T>>, usize)> {
        let head = self.head.take();
        let tail = self.tail.take();
        let len = mem::replace(&mut self.len, 0);
        if let Some(head) = head {
            // SAFETY: In a LinkedList, either both the head and tail are None because
            // the list is empty, or both head and tail are Some because the list is populated.
            // Since we have verified the head is Some, we are sure the tail is Some too.
            let tail = unsafe { tail.unwrap_unchecked() };
            Some((head, tail, len))
        } else {
            None
        }
    }

    #[inline]
    unsafe fn split_off_before_node(
        &mut self,
        split_node: Option<NonNull<Node<T>>>,
        at: usize,
    ) -> Self
    where
        A: Clone,
    {
        // The split node is the new head node of the second part
        if let Some(mut split_node) = split_node {
            let first_part_head;
            let first_part_tail;
            unsafe {
                first_part_tail = split_node.as_mut().prev.take();
            }
            if let Some(mut tail) = first_part_tail {
                unsafe {
                    tail.as_mut().next = None;
                }
                first_part_head = self.head;
            } else {
                first_part_head = None;
            }

            let first_part = LinkedList {
                head: first_part_head,
                tail: first_part_tail,
                len: at,
                alloc: self.alloc.clone(),
                marker: PhantomData,
            };

            // Fix the head ptr of the second part
            self.head = Some(split_node);
            self.len = self.len - at;

            first_part
        } else {
            mem::replace(self, LinkedList::new_in(self.alloc.clone()))
        }
    }

    #[inline]
    unsafe fn split_off_after_node(
        &mut self,
        split_node: Option<NonNull<Node<T>>>,
        at: usize,
    ) -> Self
    where
        A: Clone,
    {
        // The split node is the new tail node of the first part and owns
        // the head of the second part.
        if let Some(mut split_node) = split_node {
            let second_part_head;
            let second_part_tail;
            unsafe {
                second_part_head = split_node.as_mut().next.take();
            }
            if let Some(mut head) = second_part_head {
                unsafe {
                    head.as_mut().prev = None;
                }
                second_part_tail = self.tail;
            } else {
                second_part_tail = None;
            }

            let second_part = LinkedList {
                head: second_part_head,
                tail: second_part_tail,
                len: self.len - at,
                alloc: self.alloc.clone(),
                marker: PhantomData,
            };

            // Fix the tail ptr of the first part
            self.tail = Some(split_node);
            self.len = at;

            second_part
        } else {
            mem::replace(self, LinkedList::new_in(self.alloc.clone()))
        }
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<T> Default for LinkedList<T> {
    /// Creates an empty `LinkedList<T>`.
    #[inline]
    fn default() -> Self {
        Self::new()
    }
}

impl<T> LinkedList<T> {
    /// Creates an empty `LinkedList`.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::LinkedList;
    ///
    /// let list: LinkedList<u32> = LinkedList::new();
    /// ```
    #[inline]
    #[rustc_const_stable(feature = "const_linked_list_new", since = "1.39.0")]
    #[stable(feature = "rust1", since = "1.0.0")]
    #[must_use]
    pub const fn new() -> Self {
        LinkedList { head: None, tail: None, len: 0, alloc: Global, marker: PhantomData }
    }

    /// Moves all elements from `other` to the end of the list.
    ///
    /// This reuses all the nodes from `other` and moves them into `self`. After
    /// this operation, `other` becomes empty.
    ///
    /// This operation should compute in *O*(1) time and *O*(1) memory.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::LinkedList;
    ///
    /// let mut list1 = LinkedList::new();
    /// list1.push_back('a');
    ///
    /// let mut list2 = LinkedList::new();
    /// list2.push_back('b');
    /// list2.push_back('c');
    ///
    /// list1.append(&mut list2);
    ///
    /// let mut iter = list1.iter();
    /// assert_eq!(iter.next(), Some(&'a'));
    /// assert_eq!(iter.next(), Some(&'b'));
    /// assert_eq!(iter.next(), Some(&'c'));
    /// assert!(iter.next().is_none());
    ///
    /// assert!(list2.is_empty());
    /// ```
    #[stable(feature = "rust1", since = "1.0.0")]
    pub fn append(&mut self, other: &mut Self) {
        match self.tail {
            None => mem::swap(self, other),
            Some(mut tail) => {
                // `as_mut` is okay here because we have exclusive access to the entirety
                // of both lists.
                if let Some(mut other_head) = other.head.take() {
                    unsafe {
                        tail.as_mut().next = Some(other_head);
                        other_head.as_mut().prev = Some(tail);
                    }

                    self.tail = other.tail.take();
                    self.len += mem::replace(&mut other.len, 0);
                }
            }
        }
    }
}

impl<T, A: Allocator> LinkedList<T, A> {
    /// Constructs an empty `LinkedList<T, A>`.
    ///
    /// # Examples
    ///
    /// ```
    /// #![feature(allocator_api)]
    ///
    /// use std::alloc::System;
    /// use std::collections::LinkedList;
    ///
    /// let list: LinkedList<u32, _> = LinkedList::new_in(System);
    /// ```
    #[inline]
    #[unstable(feature = "allocator_api", issue = "32838")]
    pub const fn new_in(alloc: A) -> Self {
        LinkedList { head: None, tail: None, len: 0, alloc, marker: PhantomData }
    }
    /// Provides a forward iterator.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::LinkedList;
    ///
    /// let mut list: LinkedList<u32> = LinkedList::new();
    ///
    /// list.push_back(0);
    /// list.push_back(1);
    /// list.push_back(2);
    ///
    /// let mut iter = list.iter();
    /// assert_eq!(iter.next(), Some(&0));
    /// assert_eq!(iter.next(), Some(&1));
    /// assert_eq!(iter.next(), Some(&2));
    /// assert_eq!(iter.next(), None);
    /// ```
    #[inline]
    #[stable(feature = "rust1", since = "1.0.0")]
    pub fn iter(&self) -> Iter<'_, T> {
        Iter { head: self.head, tail: self.tail, len: self.len, marker: PhantomData }
    }

    /// Provides a forward iterator with mutable references.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::LinkedList;
    ///
    /// let mut list: LinkedList<u32> = LinkedList::new();
    ///
    /// list.push_back(0);
    /// list.push_back(1);
    /// list.push_back(2);
    ///
    /// for element in list.iter_mut() {
    ///     *element += 10;
    /// }
    ///
    /// let mut iter = list.iter();
    /// assert_eq!(iter.next(), Some(&10));
    /// assert_eq!(iter.next(), Some(&11));
    /// assert_eq!(iter.next(), Some(&12));
    /// assert_eq!(iter.next(), None);
    /// ```
    #[inline]
    #[stable(feature = "rust1", since = "1.0.0")]
    pub fn iter_mut(&mut self) -> IterMut<'_, T> {
        IterMut { head: self.head, tail: self.tail, len: self.len, marker: PhantomData }
    }

    /// Provides a cursor at the front element.
    ///
    /// The cursor is pointing to the "ghost" non-element if the list is empty.
    #[inline]
    #[must_use]
    #[unstable(feature = "linked_list_cursors", issue = "58533")]
    pub fn cursor_front(&self) -> Cursor<'_, T, A> {
        Cursor { index: 0, current: self.head, list: self }
    }

    /// Provides a cursor with editing operations at the front element.
    ///
    /// The cursor is pointing to the "ghost" non-element if the list is empty.
    #[inline]
    #[must_use]
    #[unstable(feature = "linked_list_cursors", issue = "58533")]
    pub fn cursor_front_mut(&mut self) -> CursorMut<'_, T, A> {
        CursorMut { index: 0, current: self.head, list: self }
    }

    /// Provides a cursor at the back element.
    ///
    /// The cursor is pointing to the "ghost" non-element if the list is empty.
    #[inline]
    #[must_use]
    #[unstable(feature = "linked_list_cursors", issue = "58533")]
    pub fn cursor_back(&self) -> Cursor<'_, T, A> {
        Cursor { index: self.len.checked_sub(1).unwrap_or(0), current: self.tail, list: self }
    }

    /// Provides a cursor with editing operations at the back element.
    ///
    /// The cursor is pointing to the "ghost" non-element if the list is empty.
    #[inline]
    #[must_use]
    #[unstable(feature = "linked_list_cursors", issue = "58533")]
    pub fn cursor_back_mut(&mut self) -> CursorMut<'_, T, A> {
        CursorMut { index: self.len.checked_sub(1).unwrap_or(0), current: self.tail, list: self }
    }

    /// Returns `true` if the `LinkedList` is empty.
    ///
    /// This operation should compute in *O*(1) time.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::LinkedList;
    ///
    /// let mut dl = LinkedList::new();
    /// assert!(dl.is_empty());
    ///
    /// dl.push_front("foo");
    /// assert!(!dl.is_empty());
    /// ```
    #[inline]
    #[must_use]
    #[stable(feature = "rust1", since = "1.0.0")]
    pub fn is_empty(&self) -> bool {
        self.head.is_none()
    }

    /// Returns the length of the `LinkedList`.
    ///
    /// This operation should compute in *O*(1) time.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::LinkedList;
    ///
    /// let mut dl = LinkedList::new();
    ///
    /// dl.push_front(2);
    /// assert_eq!(dl.len(), 1);
    ///
    /// dl.push_front(1);
    /// assert_eq!(dl.len(), 2);
    ///
    /// dl.push_back(3);
    /// assert_eq!(dl.len(), 3);
    /// ```
    #[inline]
    #[must_use]
    #[stable(feature = "rust1", since = "1.0.0")]
    #[rustc_confusables("length", "size")]
    pub fn len(&self) -> usize {
        self.len
    }

    /// Removes all elements from the `LinkedList`.
    ///
    /// This operation should compute in *O*(*n*) time.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::LinkedList;
    ///
    /// let mut dl = LinkedList::new();
    ///
    /// dl.push_front(2);
    /// dl.push_front(1);
    /// assert_eq!(dl.len(), 2);
    /// assert_eq!(dl.front(), Some(&1));
    ///
    /// dl.clear();
    /// assert_eq!(dl.len(), 0);
    /// assert_eq!(dl.front(), None);
    /// ```
    #[inline]
    #[stable(feature = "rust1", since = "1.0.0")]
    pub fn clear(&mut self) {
        // We need to drop the nodes while keeping self.alloc
        // We can do this by moving (head, tail, len) into a new list that borrows self.alloc
        drop(LinkedList {
            head: self.head.take(),
            tail: self.tail.take(),
            len: mem::take(&mut self.len),
            alloc: &self.alloc,
            marker: PhantomData,
        });
    }

    /// Returns `true` if the `LinkedList` contains an element equal to the
    /// given value.
    ///
    /// This operation should compute linearly in *O*(*n*) time.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::LinkedList;
    ///
    /// let mut list: LinkedList<u32> = LinkedList::new();
    ///
    /// list.push_back(0);
    /// list.push_back(1);
    /// list.push_back(2);
    ///
    /// assert_eq!(list.contains(&0), true);
    /// assert_eq!(list.contains(&10), false);
    /// ```
    #[stable(feature = "linked_list_contains", since = "1.12.0")]
    pub fn contains(&self, x: &T) -> bool
    where
        T: PartialEq<T>,
    {
        self.iter().any(|e| e == x)
    }

    /// Provides a reference to the front element, or `None` if the list is
    /// empty.
    ///
    /// This operation should compute in *O*(1) time.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::LinkedList;
    ///
    /// let mut dl = LinkedList::new();
    /// assert_eq!(dl.front(), None);
    ///
    /// dl.push_front(1);
    /// assert_eq!(dl.front(), Some(&1));
    /// ```
    #[inline]
    #[must_use]
    #[stable(feature = "rust1", since = "1.0.0")]
    #[rustc_confusables("first")]
    pub fn front(&self) -> Option<&T> {
        unsafe { self.head.as_ref().map(|node| &node.as_ref().element) }
    }

    /// Provides a mutable reference to the front element, or `None` if the list
    /// is empty.
    ///
    /// This operation should compute in *O*(1) time.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::LinkedList;
    ///
    /// let mut dl = LinkedList::new();
    /// assert_eq!(dl.front(), None);
    ///
    /// dl.push_front(1);
    /// assert_eq!(dl.front(), Some(&1));
    ///
    /// match dl.front_mut() {
    ///     None => {},
    ///     Some(x) => *x = 5,
    /// }
    /// assert_eq!(dl.front(), Some(&5));
    /// ```
    #[inline]
    #[must_use]
    #[stable(feature = "rust1", since = "1.0.0")]
    pub fn front_mut(&mut self) -> Option<&mut T> {
        unsafe { self.head.as_mut().map(|node| &mut node.as_mut().element) }
    }

    /// Provides a reference to the back element, or `None` if the list is
    /// empty.
    ///
    /// This operation should compute in *O*(1) time.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::LinkedList;
    ///
    /// let mut dl = LinkedList::new();
    /// assert_eq!(dl.back(), None);
    ///
    /// dl.push_back(1);
    /// assert_eq!(dl.back(), Some(&1));
    /// ```
    #[inline]
    #[must_use]
    #[stable(feature = "rust1", since = "1.0.0")]
    pub fn back(&self) -> Option<&T> {
        unsafe { self.tail.as_ref().map(|node| &node.as_ref().element) }
    }

    /// Provides a mutable reference to the back element, or `None` if the list
    /// is empty.
    ///
    /// This operation should compute in *O*(1) time.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::LinkedList;
    ///
    /// let mut dl = LinkedList::new();
    /// assert_eq!(dl.back(), None);
    ///
    /// dl.push_back(1);
    /// assert_eq!(dl.back(), Some(&1));
    ///
    /// match dl.back_mut() {
    ///     None => {},
    ///     Some(x) => *x = 5,
    /// }
    /// assert_eq!(dl.back(), Some(&5));
    /// ```
    #[inline]
    #[stable(feature = "rust1", since = "1.0.0")]
    pub fn back_mut(&mut self) -> Option<&mut T> {
        unsafe { self.tail.as_mut().map(|node| &mut node.as_mut().element) }
    }

    /// Adds an element first in the list.
    ///
    /// This operation should compute in *O*(1) time.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::LinkedList;
    ///
    /// let mut dl = LinkedList::new();
    ///
    /// dl.push_front(2);
    /// assert_eq!(dl.front().unwrap(), &2);
    ///
    /// dl.push_front(1);
    /// assert_eq!(dl.front().unwrap(), &1);
    /// ```
    #[stable(feature = "rust1", since = "1.0.0")]
    pub fn push_front(&mut self, elt: T) {
        let node = Box::new_in(Node::new(elt), &self.alloc);
        let node_ptr = NonNull::from(Box::leak(node));
        // SAFETY: node_ptr is a unique pointer to a node we boxed with self.alloc and leaked
        unsafe {
            self.push_front_node(node_ptr);
        }
    }

    /// Removes the first element and returns it, or `None` if the list is
    /// empty.
    ///
    /// This operation should compute in *O*(1) time.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::LinkedList;
    ///
    /// let mut d = LinkedList::new();
    /// assert_eq!(d.pop_front(), None);
    ///
    /// d.push_front(1);
    /// d.push_front(3);
    /// assert_eq!(d.pop_front(), Some(3));
    /// assert_eq!(d.pop_front(), Some(1));
    /// assert_eq!(d.pop_front(), None);
    /// ```
    #[stable(feature = "rust1", since = "1.0.0")]
    pub fn pop_front(&mut self) -> Option<T> {
        self.pop_front_node().map(Node::into_element)
    }

    /// Appends an element to the back of a list.
    ///
    /// This operation should compute in *O*(1) time.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::LinkedList;
    ///
    /// let mut d = LinkedList::new();
    /// d.push_back(1);
    /// d.push_back(3);
    /// assert_eq!(3, *d.back().unwrap());
    /// ```
    #[stable(feature = "rust1", since = "1.0.0")]
    #[rustc_confusables("push", "append")]
    pub fn push_back(&mut self, elt: T) {
        let node = Box::new_in(Node::new(elt), &self.alloc);
        let node_ptr = NonNull::from(Box::leak(node));
        // SAFETY: node_ptr is a unique pointer to a node we boxed with self.alloc and leaked
        unsafe {
            self.push_back_node(node_ptr);
        }
    }

    /// Removes the last element from a list and returns it, or `None` if
    /// it is empty.
    ///
    /// This operation should compute in *O*(1) time.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::LinkedList;
    ///
    /// let mut d = LinkedList::new();
    /// assert_eq!(d.pop_back(), None);
    /// d.push_back(1);
    /// d.push_back(3);
    /// assert_eq!(d.pop_back(), Some(3));
    /// ```
    #[stable(feature = "rust1", since = "1.0.0")]
    pub fn pop_back(&mut self) -> Option<T> {
        self.pop_back_node().map(Node::into_element)
    }

    /// Splits the list into two at the given index. Returns everything after the given index,
    /// including the index.
    ///
    /// This operation should compute in *O*(*n*) time.
    ///
    /// # Panics
    ///
    /// Panics if `at > len`.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::LinkedList;
    ///
    /// let mut d = LinkedList::new();
    ///
    /// d.push_front(1);
    /// d.push_front(2);
    /// d.push_front(3);
    ///
    /// let mut split = d.split_off(2);
    ///
    /// assert_eq!(split.pop_front(), Some(1));
    /// assert_eq!(split.pop_front(), None);
    /// ```
    #[stable(feature = "rust1", since = "1.0.0")]
    pub fn split_off(&mut self, at: usize) -> LinkedList<T, A>
    where
        A: Clone,
    {
        let len = self.len();
        assert!(at <= len, "Cannot split off at a nonexistent index");
        if at == 0 {
            return mem::replace(self, Self::new_in(self.alloc.clone()));
        } else if at == len {
            return Self::new_in(self.alloc.clone());
        }

        // Below, we iterate towards the `i-1`th node, either from the start or the end,
        // depending on which would be faster.
        let split_node = if at - 1 <= len - 1 - (at - 1) {
            let mut iter = self.iter_mut();
            // instead of skipping using .skip() (which creates a new struct),
            // we skip manually so we can access the head field without
            // depending on implementation details of Skip
            for _ in 0..at - 1 {
                iter.next();
            }
            iter.head
        } else {
            // better off starting from the end
            let mut iter = self.iter_mut();
            for _ in 0..len - 1 - (at - 1) {
                iter.next_back();
            }
            iter.tail
        };
        unsafe { self.split_off_after_node(split_node, at) }
    }

    /// Removes the element at the given index and returns it.
    ///
    /// This operation should compute in *O*(*n*) time.
    ///
    /// # Panics
    /// Panics if at >= len
    ///
    /// # Examples
    ///
    /// ```
    /// #![feature(linked_list_remove)]
    /// use std::collections::LinkedList;
    ///
    /// let mut d = LinkedList::new();
    ///
    /// d.push_front(1);
    /// d.push_front(2);
    /// d.push_front(3);
    ///
    /// assert_eq!(d.remove(1), 2);
    /// assert_eq!(d.remove(0), 3);
    /// assert_eq!(d.remove(0), 1);
    /// ```
    #[unstable(feature = "linked_list_remove", issue = "69210")]
    #[rustc_confusables("delete", "take")]
    pub fn remove(&mut self, at: usize) -> T {
        let len = self.len();
        assert!(at < len, "Cannot remove at an index outside of the list bounds");

        // Below, we iterate towards the node at the given index, either from
        // the start or the end, depending on which would be faster.
        let offset_from_end = len - at - 1;
        if at <= offset_from_end {
            let mut cursor = self.cursor_front_mut();
            for _ in 0..at {
                cursor.move_next();
            }
            cursor.remove_current().unwrap()
        } else {
            let mut cursor = self.cursor_back_mut();
            for _ in 0..offset_from_end {
                cursor.move_prev();
            }
            cursor.remove_current().unwrap()
        }
    }

    /// Retains only the elements specified by the predicate.
    ///
    /// In other words, remove all elements `e` for which `f(&e)` returns false.
    /// This method operates in place, visiting each element exactly once in the
    /// original order, and preserves the order of the retained elements.
    ///
    /// # Examples
    ///
    /// ```
    /// #![feature(linked_list_retain)]
    /// use std::collections::LinkedList;
    ///
    /// let mut d = LinkedList::new();
    ///
    /// d.push_front(1);
    /// d.push_front(2);
    /// d.push_front(3);
    ///
    /// d.retain(|&x| x % 2 == 0);
    ///
    /// assert_eq!(d.pop_front(), Some(2));
    /// assert_eq!(d.pop_front(), None);
    /// ```
    ///
    /// Because the elements are visited exactly once in the original order,
    /// external state may be used to decide which elements to keep.
    ///
    /// ```
    /// #![feature(linked_list_retain)]
    /// use std::collections::LinkedList;
    ///
    /// let mut d = LinkedList::new();
    ///
    /// d.push_front(1);
    /// d.push_front(2);
    /// d.push_front(3);
    ///
    /// let keep = [false, true, false];
    /// let mut iter = keep.iter();
    /// d.retain(|_| *iter.next().unwrap());
    /// assert_eq!(d.pop_front(), Some(2));
    /// assert_eq!(d.pop_front(), None);
    /// ```
    #[unstable(feature = "linked_list_retain", issue = "114135")]
    pub fn retain<F>(&mut self, mut f: F)
    where
        F: FnMut(&T) -> bool,
    {
        self.retain_mut(|elem| f(elem));
    }

    /// Retains only the elements specified by the predicate.
    ///
    /// In other words, remove all elements `e` for which `f(&mut e)` returns false.
    /// This method operates in place, visiting each element exactly once in the
    /// original order, and preserves the order of the retained elements.
    ///
    /// # Examples
    ///
    /// ```
    /// #![feature(linked_list_retain)]
    /// use std::collections::LinkedList;
    ///
    /// let mut d = LinkedList::new();
    ///
    /// d.push_front(1);
    /// d.push_front(2);
    /// d.push_front(3);
    ///
    /// d.retain_mut(|x| if *x % 2 == 0 {
    ///     *x += 1;
    ///     true
    /// } else {
    ///     false
    /// });
    /// assert_eq!(d.pop_front(), Some(3));
    /// assert_eq!(d.pop_front(), None);
    /// ```
    #[unstable(feature = "linked_list_retain", issue = "114135")]
    pub fn retain_mut<F>(&mut self, mut f: F)
    where
        F: FnMut(&mut T) -> bool,
    {
        let mut cursor = self.cursor_front_mut();
        while let Some(node) = cursor.current() {
            if !f(node) {
                cursor.remove_current().unwrap();
            } else {
                cursor.move_next();
            }
        }
    }

    /// Creates an iterator which uses a closure to determine if an element should be removed.
    ///
    /// If the closure returns true, then the element is removed and yielded.
    /// If the closure returns false, the element will remain in the list and will not be yielded
    /// by the iterator.
    ///
    /// If the returned `ExtractIf` is not exhausted, e.g. because it is dropped without iterating
    /// or the iteration short-circuits, then the remaining elements will be retained.
    /// Use `extract_if().for_each(drop)` if you do not need the returned iterator.
    ///
    /// Note that `extract_if` lets you mutate every element in the filter closure, regardless of
    /// whether you choose to keep or remove it.
    ///
    /// # Examples
    ///
    /// Splitting a list into evens and odds, reusing the original list:
    ///
    /// ```
    /// #![feature(extract_if)]
    /// use std::collections::LinkedList;
    ///
    /// let mut numbers: LinkedList<u32> = LinkedList::new();
    /// numbers.extend(&[1, 2, 3, 4, 5, 6, 8, 9, 11, 13, 14, 15]);
    ///
    /// let evens = numbers.extract_if(|x| *x % 2 == 0).collect::<LinkedList<_>>();
    /// let odds = numbers;
    ///
    /// assert_eq!(evens.into_iter().collect::<Vec<_>>(), vec![2, 4, 6, 8, 14]);
    /// assert_eq!(odds.into_iter().collect::<Vec<_>>(), vec![1, 3, 5, 9, 11, 13, 15]);
    /// ```
    #[unstable(feature = "extract_if", reason = "recently added", issue = "43244")]
    pub fn extract_if<F>(&mut self, filter: F) -> ExtractIf<'_, T, F, A>
    where
        F: FnMut(&mut T) -> bool,
    {
        // avoid borrow issues.
        let it = self.head;
        let old_len = self.len;

        ExtractIf { list: self, it, pred: filter, idx: 0, old_len }
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
unsafe impl<#[may_dangle] T, A: Allocator> Drop for LinkedList<T, A> {
    fn drop(&mut self) {
        struct DropGuard<'a, T, A: Allocator>(&'a mut LinkedList<T, A>);

        impl<'a, T, A: Allocator> Drop for DropGuard<'a, T, A> {
            fn drop(&mut self) {
                // Continue the same loop we do below. This only runs when a destructor has
                // panicked. If another one panics this will abort.
                while self.0.pop_front_node().is_some() {}
            }
        }

        // Wrap self so that if a destructor panics, we can try to keep looping
        let guard = DropGuard(self);
        while guard.0.pop_front_node().is_some() {}
        mem::forget(guard);
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<'a, T> Iterator for Iter<'a, T> {
    type Item = &'a T;

    #[inline]
    fn next(&mut self) -> Option<&'a T> {
        if self.len == 0 {
            None
        } else {
            self.head.map(|node| unsafe {
                // Need an unbound lifetime to get 'a
                let node = &*node.as_ptr();
                self.len -= 1;
                self.head = node.next;
                &node.element
            })
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len, Some(self.len))
    }

    #[inline]
    fn last(mut self) -> Option<&'a T> {
        self.next_back()
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<'a, T> DoubleEndedIterator for Iter<'a, T> {
    #[inline]
    fn next_back(&mut self) -> Option<&'a T> {
        if self.len == 0 {
            None
        } else {
            self.tail.map(|node| unsafe {
                // Need an unbound lifetime to get 'a
                let node = &*node.as_ptr();
                self.len -= 1;
                self.tail = node.prev;
                &node.element
            })
        }
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<T> ExactSizeIterator for Iter<'_, T> {}

#[stable(feature = "fused", since = "1.26.0")]
impl<T> FusedIterator for Iter<'_, T> {}

#[stable(feature = "default_iters", since = "1.70.0")]
impl<T> Default for Iter<'_, T> {
    /// Creates an empty `linked_list::Iter`.
    ///
    /// ```
    /// # use std::collections::linked_list;
    /// let iter: linked_list::Iter<'_, u8> = Default::default();
    /// assert_eq!(iter.len(), 0);
    /// ```
    fn default() -> Self {
        Iter { head: None, tail: None, len: 0, marker: Default::default() }
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<'a, T> Iterator for IterMut<'a, T> {
    type Item = &'a mut T;

    #[inline]
    fn next(&mut self) -> Option<&'a mut T> {
        if self.len == 0 {
            None
        } else {
            self.head.map(|node| unsafe {
                // Need an unbound lifetime to get 'a
                let node = &mut *node.as_ptr();
                self.len -= 1;
                self.head = node.next;
                &mut node.element
            })
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len, Some(self.len))
    }

    #[inline]
    fn last(mut self) -> Option<&'a mut T> {
        self.next_back()
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<'a, T> DoubleEndedIterator for IterMut<'a, T> {
    #[inline]
    fn next_back(&mut self) -> Option<&'a mut T> {
        if self.len == 0 {
            None
        } else {
            self.tail.map(|node| unsafe {
                // Need an unbound lifetime to get 'a
                let node = &mut *node.as_ptr();
                self.len -= 1;
                self.tail = node.prev;
                &mut node.element
            })
        }
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<T> ExactSizeIterator for IterMut<'_, T> {}

#[stable(feature = "fused", since = "1.26.0")]
impl<T> FusedIterator for IterMut<'_, T> {}

#[stable(feature = "default_iters", since = "1.70.0")]
impl<T> Default for IterMut<'_, T> {
    fn default() -> Self {
        IterMut { head: None, tail: None, len: 0, marker: Default::default() }
    }
}

/// A cursor over a `LinkedList`.
///
/// A `Cursor` is like an iterator, except that it can freely seek back-and-forth.
///
/// Cursors always rest between two elements in the list, and index in a logically circular way.
/// To accommodate this, there is a "ghost" non-element that yields `None` between the head and
/// tail of the list.
///
/// When created, cursors start at the front of the list, or the "ghost" non-element if the list is empty.
#[unstable(feature = "linked_list_cursors", issue = "58533")]
pub struct Cursor<
    'a,
    T: 'a,
    #[unstable(feature = "allocator_api", issue = "32838")] A: Allocator = Global,
> {
    index: usize,
    current: Option<NonNull<Node<T>>>,
    list: &'a LinkedList<T, A>,
}

#[unstable(feature = "linked_list_cursors", issue = "58533")]
impl<T, A: Allocator> Clone for Cursor<'_, T, A> {
    fn clone(&self) -> Self {
        let Cursor { index, current, list } = *self;
        Cursor { index, current, list }
    }
}

#[unstable(feature = "linked_list_cursors", issue = "58533")]
impl<T: fmt::Debug, A: Allocator> fmt::Debug for Cursor<'_, T, A> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("Cursor").field(&self.list).field(&self.index()).finish()
    }
}

/// A cursor over a `LinkedList` with editing operations.
///
/// A `Cursor` is like an iterator, except that it can freely seek back-and-forth, and can
/// safely mutate the list during iteration. This is because the lifetime of its yielded
/// references is tied to its own lifetime, instead of just the underlying list. This means
/// cursors cannot yield multiple elements at once.
///
/// Cursors always rest between two elements in the list, and index in a logically circular way.
/// To accommodate this, there is a "ghost" non-element that yields `None` between the head and
/// tail of the list.
#[unstable(feature = "linked_list_cursors", issue = "58533")]
pub struct CursorMut<
    'a,
    T: 'a,
    #[unstable(feature = "allocator_api", issue = "32838")] A: Allocator = Global,
> {
    index: usize,
    current: Option<NonNull<Node<T>>>,
    list: &'a mut LinkedList<T, A>,
}

#[unstable(feature = "linked_list_cursors", issue = "58533")]
impl<T: fmt::Debug, A: Allocator> fmt::Debug for CursorMut<'_, T, A> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("CursorMut").field(&self.list).field(&self.index()).finish()
    }
}

impl<'a, T, A: Allocator> Cursor<'a, T, A> {
    /// Returns the cursor position index within the `LinkedList`.
    ///
    /// This returns `None` if the cursor is currently pointing to the
    /// "ghost" non-element.
    #[must_use]
    #[unstable(feature = "linked_list_cursors", issue = "58533")]
    pub fn index(&self) -> Option<usize> {
        let _ = self.current?;
        Some(self.index)
    }

    /// Moves the cursor to the next element of the `LinkedList`.
    ///
    /// If the cursor is pointing to the "ghost" non-element then this will move it to
    /// the first element of the `LinkedList`. If it is pointing to the last
    /// element of the `LinkedList` then this will move it to the "ghost" non-element.
    #[unstable(feature = "linked_list_cursors", issue = "58533")]
    pub fn move_next(&mut self) {
        match self.current.take() {
            // We had no current element; the cursor was sitting at the start position
            // Next element should be the head of the list
            None => {
                self.current = self.list.head;
                self.index = 0;
            }
            // We had a previous element, so let's go to its next
            Some(current) => unsafe {
                self.current = current.as_ref().next;
                self.index += 1;
            },
        }
    }

    /// Moves the cursor to the previous element of the `LinkedList`.
    ///
    /// If the cursor is pointing to the "ghost" non-element then this will move it to
    /// the last element of the `LinkedList`. If it is pointing to the first
    /// element of the `LinkedList` then this will move it to the "ghost" non-element.
    #[unstable(feature = "linked_list_cursors", issue = "58533")]
    pub fn move_prev(&mut self) {
        match self.current.take() {
            // No current. We're at the start of the list. Yield None and jump to the end.
            None => {
                self.current = self.list.tail;
                self.index = self.list.len().checked_sub(1).unwrap_or(0);
            }
            // Have a prev. Yield it and go to the previous element.
            Some(current) => unsafe {
                self.current = current.as_ref().prev;
                self.index = self.index.checked_sub(1).unwrap_or_else(|| self.list.len());
            },
        }
    }

    /// Returns a reference to the element that the cursor is currently
    /// pointing to.
    ///
    /// This returns `None` if the cursor is currently pointing to the
    /// "ghost" non-element.
    #[must_use]
    #[unstable(feature = "linked_list_cursors", issue = "58533")]
    pub fn current(&self) -> Option<&'a T> {
        unsafe { self.current.map(|current| &(*current.as_ptr()).element) }
    }

    /// Returns a reference to the next element.
    ///
    /// If the cursor is pointing to the "ghost" non-element then this returns
    /// the first element of the `LinkedList`. If it is pointing to the last
    /// element of the `LinkedList` then this returns `None`.
    #[must_use]
    #[unstable(feature = "linked_list_cursors", issue = "58533")]
    pub fn peek_next(&self) -> Option<&'a T> {
        unsafe {
            let next = match self.current {
                None => self.list.head,
                Some(current) => current.as_ref().next,
            };
            next.map(|next| &(*next.as_ptr()).element)
        }
    }

    /// Returns a reference to the previous element.
    ///
    /// If the cursor is pointing to the "ghost" non-element then this returns
    /// the last element of the `LinkedList`. If it is pointing to the first
    /// element of the `LinkedList` then this returns `None`.
    #[must_use]
    #[unstable(feature = "linked_list_cursors", issue = "58533")]
    pub fn peek_prev(&self) -> Option<&'a T> {
        unsafe {
            let prev = match self.current {
                None => self.list.tail,
                Some(current) => current.as_ref().prev,
            };
            prev.map(|prev| &(*prev.as_ptr()).element)
        }
    }

    /// Provides a reference to the front element of the cursor's parent list,
    /// or None if the list is empty.
    #[must_use]
    #[unstable(feature = "linked_list_cursors", issue = "58533")]
    #[rustc_confusables("first")]
    pub fn front(&self) -> Option<&'a T> {
        self.list.front()
    }

    /// Provides a reference to the back element of the cursor's parent list,
    /// or None if the list is empty.
    #[must_use]
    #[unstable(feature = "linked_list_cursors", issue = "58533")]
    #[rustc_confusables("last")]
    pub fn back(&self) -> Option<&'a T> {
        self.list.back()
    }

    /// Provides a reference to the cursor's parent list.
    #[must_use]
    #[inline(always)]
    #[unstable(feature = "linked_list_cursors", issue = "58533")]
    pub fn as_list(&self) -> &'a LinkedList<T, A> {
        self.list
    }
}

impl<'a, T, A: Allocator> CursorMut<'a, T, A> {
    /// Returns the cursor position index within the `LinkedList`.
    ///
    /// This returns `None` if the cursor is currently pointing to the
    /// "ghost" non-element.
    #[must_use]
    #[unstable(feature = "linked_list_cursors", issue = "58533")]
    pub fn index(&self) -> Option<usize> {
        let _ = self.current?;
        Some(self.index)
    }

    /// Moves the cursor to the next element of the `LinkedList`.
    ///
    /// If the cursor is pointing to the "ghost" non-element then this will move it to
    /// the first element of the `LinkedList`. If it is pointing to the last
    /// element of the `LinkedList` then this will move it to the "ghost" non-element.
    #[unstable(feature = "linked_list_cursors", issue = "58533")]
    pub fn move_next(&mut self) {
        match self.current.take() {
            // We had no current element; the cursor was sitting at the start position
            // Next element should be the head of the list
            None => {
                self.current = self.list.head;
                self.index = 0;
            }
            // We had a previous element, so let's go to its next
            Some(current) => unsafe {
                self.current = current.as_ref().next;
                self.index += 1;
            },
        }
    }

    /// Moves the cursor to the previous element of the `LinkedList`.
    ///
    /// If the cursor is pointing to the "ghost" non-element then this will move it to
    /// the last element of the `LinkedList`. If it is pointing to the first
    /// element of the `LinkedList` then this will move it to the "ghost" non-element.
    #[unstable(feature = "linked_list_cursors", issue = "58533")]
    pub fn move_prev(&mut self) {
        match self.current.take() {
            // No current. We're at the start of the list. Yield None and jump to the end.
            None => {
                self.current = self.list.tail;
                self.index = self.list.len().checked_sub(1).unwrap_or(0);
            }
            // Have a prev. Yield it and go to the previous element.
            Some(current) => unsafe {
                self.current = current.as_ref().prev;
                self.index = self.index.checked_sub(1).unwrap_or_else(|| self.list.len());
            },
        }
    }

    /// Returns a reference to the element that the cursor is currently
    /// pointing to.
    ///
    /// This returns `None` if the cursor is currently pointing to the
    /// "ghost" non-element.
    #[must_use]
    #[unstable(feature = "linked_list_cursors", issue = "58533")]
    pub fn current(&mut self) -> Option<&mut T> {
        unsafe { self.current.map(|current| &mut (*current.as_ptr()).element) }
    }

    /// Returns a reference to the next element.
    ///
    /// If the cursor is pointing to the "ghost" non-element then this returns
    /// the first element of the `LinkedList`. If it is pointing to the last
    /// element of the `LinkedList` then this returns `None`.
    #[unstable(feature = "linked_list_cursors", issue = "58533")]
    pub fn peek_next(&mut self) -> Option<&mut T> {
        unsafe {
            let next = match self.current {
                None => self.list.head,
                Some(current) => current.as_ref().next,
            };
            next.map(|next| &mut (*next.as_ptr()).element)
        }
    }

    /// Returns a reference to the previous element.
    ///
    /// If the cursor is pointing to the "ghost" non-element then this returns
    /// the last element of the `LinkedList`. If it is pointing to the first
    /// element of the `LinkedList` then this returns `None`.
    #[unstable(feature = "linked_list_cursors", issue = "58533")]
    pub fn peek_prev(&mut self) -> Option<&mut T> {
        unsafe {
            let prev = match self.current {
                None => self.list.tail,
                Some(current) => current.as_ref().prev,
            };
            prev.map(|prev| &mut (*prev.as_ptr()).element)
        }
    }

    /// Returns a read-only cursor pointing to the current element.
    ///
    /// The lifetime of the returned `Cursor` is bound to that of the
    /// `CursorMut`, which means it cannot outlive the `CursorMut` and that the
    /// `CursorMut` is frozen for the lifetime of the `Cursor`.
    #[must_use]
    #[unstable(feature = "linked_list_cursors", issue = "58533")]
    pub fn as_cursor(&self) -> Cursor<'_, T, A> {
        Cursor { list: self.list, current: self.current, index: self.index }
    }

    /// Provides a read-only reference to the cursor's parent list.
    ///
    /// The lifetime of the returned reference is bound to that of the
    /// `CursorMut`, which means it cannot outlive the `CursorMut` and that the
    /// `CursorMut` is frozen for the lifetime of the reference.
    #[must_use]
    #[inline(always)]
    #[unstable(feature = "linked_list_cursors", issue = "58533")]
    pub fn as_list(&self) -> &LinkedList<T, A> {
        self.list
    }
}

// Now the list editing operations

impl<'a, T> CursorMut<'a, T> {
    /// Inserts the elements from the given `LinkedList` after the current one.
    ///
    /// If the cursor is pointing at the "ghost" non-element then the new elements are
    /// inserted at the start of the `LinkedList`.
    #[unstable(feature = "linked_list_cursors", issue = "58533")]
    pub fn splice_after(&mut self, list: LinkedList<T>) {
        unsafe {
            let (splice_head, splice_tail, splice_len) = match list.detach_all_nodes() {
                Some(parts) => parts,
                _ => return,
            };
            let node_next = match self.current {
                None => self.list.head,
                Some(node) => node.as_ref().next,
            };
            self.list.splice_nodes(self.current, node_next, splice_head, splice_tail, splice_len);
            if self.current.is_none() {
                // The "ghost" non-element's index has changed.
                self.index = self.list.len;
            }
        }
    }

    /// Inserts the elements from the given `LinkedList` before the current one.
    ///
    /// If the cursor is pointing at the "ghost" non-element then the new elements are
    /// inserted at the end of the `LinkedList`.
    #[unstable(feature = "linked_list_cursors", issue = "58533")]
    pub fn splice_before(&mut self, list: LinkedList<T>) {
        unsafe {
            let (splice_head, splice_tail, splice_len) = match list.detach_all_nodes() {
                Some(parts) => parts,
                _ => return,
            };
            let node_prev = match self.current {
                None => self.list.tail,
                Some(node) => node.as_ref().prev,
            };
            self.list.splice_nodes(node_prev, self.current, splice_head, splice_tail, splice_len);
            self.index += splice_len;
        }
    }
}

impl<'a, T, A: Allocator> CursorMut<'a, T, A> {
    /// Inserts a new element into the `LinkedList` after the current one.
    ///
    /// If the cursor is pointing at the "ghost" non-element then the new element is
    /// inserted at the front of the `LinkedList`.
    #[unstable(feature = "linked_list_cursors", issue = "58533")]
    pub fn insert_after(&mut self, item: T) {
        unsafe {
            let spliced_node = Box::leak(Box::new_in(Node::new(item), &self.list.alloc)).into();
            let node_next = match self.current {
                None => self.list.head,
                Some(node) => node.as_ref().next,
            };
            self.list.splice_nodes(self.current, node_next, spliced_node, spliced_node, 1);
            if self.current.is_none() {
                // The "ghost" non-element's index has changed.
                self.index = self.list.len;
            }
        }
    }

    /// Inserts a new element into the `LinkedList` before the current one.
    ///
    /// If the cursor is pointing at the "ghost" non-element then the new element is
    /// inserted at the end of the `LinkedList`.
    #[unstable(feature = "linked_list_cursors", issue = "58533")]
    pub fn insert_before(&mut self, item: T) {
        unsafe {
            let spliced_node = Box::leak(Box::new_in(Node::new(item), &self.list.alloc)).into();
            let node_prev = match self.current {
                None => self.list.tail,
                Some(node) => node.as_ref().prev,
            };
            self.list.splice_nodes(node_prev, self.current, spliced_node, spliced_node, 1);
            self.index += 1;
        }
    }

    /// Removes the current element from the `LinkedList`.
    ///
    /// The element that was removed is returned, and the cursor is
    /// moved to point to the next element in the `LinkedList`.
    ///
    /// If the cursor is currently pointing to the "ghost" non-element then no element
    /// is removed and `None` is returned.
    #[unstable(feature = "linked_list_cursors", issue = "58533")]
    pub fn remove_current(&mut self) -> Option<T> {
        let unlinked_node = self.current?;
        unsafe {
            self.current = unlinked_node.as_ref().next;
            self.list.unlink_node(unlinked_node);
            let unlinked_node = Box::from_raw_in(unlinked_node.as_ptr(), &self.list.alloc);
            Some(unlinked_node.element)
        }
    }

    /// Removes the current element from the `LinkedList` without deallocating the list node.
    ///
    /// The node that was removed is returned as a new `LinkedList` containing only this node.
    /// The cursor is moved to point to the next element in the current `LinkedList`.
    ///
    /// If the cursor is currently pointing to the "ghost" non-element then no element
    /// is removed and `None` is returned.
    #[unstable(feature = "linked_list_cursors", issue = "58533")]
    pub fn remove_current_as_list(&mut self) -> Option<LinkedList<T, A>>
    where
        A: Clone,
    {
        let mut unlinked_node = self.current?;
        unsafe {
            self.current = unlinked_node.as_ref().next;
            self.list.unlink_node(unlinked_node);

            unlinked_node.as_mut().prev = None;
            unlinked_node.as_mut().next = None;
            Some(LinkedList {
                head: Some(unlinked_node),
                tail: Some(unlinked_node),
                len: 1,
                alloc: self.list.alloc.clone(),
                marker: PhantomData,
            })
        }
    }

    /// Splits the list into two after the current element. This will return a
    /// new list consisting of everything after the cursor, with the original
    /// list retaining everything before.
    ///
    /// If the cursor is pointing at the "ghost" non-element then the entire contents
    /// of the `LinkedList` are moved.
    #[unstable(feature = "linked_list_cursors", issue = "58533")]
    pub fn split_after(&mut self) -> LinkedList<T, A>
    where
        A: Clone,
    {
        let split_off_idx = if self.index == self.list.len { 0 } else { self.index + 1 };
        if self.index == self.list.len {
            // The "ghost" non-element's index has changed to 0.
            self.index = 0;
        }
        unsafe { self.list.split_off_after_node(self.current, split_off_idx) }
    }

    /// Splits the list into two before the current element. This will return a
    /// new list consisting of everything before the cursor, with the original
    /// list retaining everything after.
    ///
    /// If the cursor is pointing at the "ghost" non-element then the entire contents
    /// of the `LinkedList` are moved.
    #[unstable(feature = "linked_list_cursors", issue = "58533")]
    pub fn split_before(&mut self) -> LinkedList<T, A>
    where
        A: Clone,
    {
        let split_off_idx = self.index;
        self.index = 0;
        unsafe { self.list.split_off_before_node(self.current, split_off_idx) }
    }

    /// Appends an element to the front of the cursor's parent list. The node
    /// that the cursor points to is unchanged, even if it is the "ghost" node.
    ///
    /// This operation should compute in *O*(1) time.
    // `push_front` continues to point to "ghost" when it adds a node to mimic
    // the behavior of `insert_before` on an empty list.
    #[unstable(feature = "linked_list_cursors", issue = "58533")]
    pub fn push_front(&mut self, elt: T) {
        // Safety: We know that `push_front` does not change the position in
        // memory of other nodes. This ensures that `self.current` remains
        // valid.
        self.list.push_front(elt);
        self.index += 1;
    }

    /// Appends an element to the back of the cursor's parent list. The node
    /// that the cursor points to is unchanged, even if it is the "ghost" node.
    ///
    /// This operation should compute in *O*(1) time.
    #[unstable(feature = "linked_list_cursors", issue = "58533")]
    #[rustc_confusables("push", "append")]
    pub fn push_back(&mut self, elt: T) {
        // Safety: We know that `push_back` does not change the position in
        // memory of other nodes. This ensures that `self.current` remains
        // valid.
        self.list.push_back(elt);
        if self.current().is_none() {
            // The index of "ghost" is the length of the list, so we just need
            // to increment self.index to reflect the new length of the list.
            self.index += 1;
        }
    }

    /// Removes the first element from the cursor's parent list and returns it,
    /// or None if the list is empty. The element the cursor points to remains
    /// unchanged, unless it was pointing to the front element. In that case, it
    /// points to the new front element.
    ///
    /// This operation should compute in *O*(1) time.
    #[unstable(feature = "linked_list_cursors", issue = "58533")]
    pub fn pop_front(&mut self) -> Option<T> {
        // We can't check if current is empty, we must check the list directly.
        // It is possible for `self.current == None` and the list to be
        // non-empty.
        if self.list.is_empty() {
            None
        } else {
            // We can't point to the node that we pop. Copying the behavior of
            // `remove_current`, we move on to the next node in the sequence.
            // If the list is of length 1 then we end pointing to the "ghost"
            // node at index 0, which is expected.
            if self.list.head == self.current {
                self.move_next();
            } else {
                self.index -= 1;
            }
            self.list.pop_front()
        }
    }

    /// Removes the last element from the cursor's parent list and returns it,
    /// or None if the list is empty. The element the cursor points to remains
    /// unchanged, unless it was pointing to the back element. In that case, it
    /// points to the "ghost" element.
    ///
    /// This operation should compute in *O*(1) time.
    #[unstable(feature = "linked_list_cursors", issue = "58533")]
    #[rustc_confusables("pop")]
    pub fn pop_back(&mut self) -> Option<T> {
        if self.list.is_empty() {
            None
        } else {
            if self.list.tail == self.current {
                // The index now reflects the length of the list. It was the
                // length of the list minus 1, but now the list is 1 smaller. No
                // change is needed for `index`.
                self.current = None;
            } else if self.current.is_none() {
                self.index = self.list.len - 1;
            }
            self.list.pop_back()
        }
    }

    /// Provides a reference to the front element of the cursor's parent list,
    /// or None if the list is empty.
    #[must_use]
    #[unstable(feature = "linked_list_cursors", issue = "58533")]
    #[rustc_confusables("first")]
    pub fn front(&self) -> Option<&T> {
        self.list.front()
    }

    /// Provides a mutable reference to the front element of the cursor's
    /// parent list, or None if the list is empty.
    #[must_use]
    #[unstable(feature = "linked_list_cursors", issue = "58533")]
    pub fn front_mut(&mut self) -> Option<&mut T> {
        self.list.front_mut()
    }

    /// Provides a reference to the back element of the cursor's parent list,
    /// or None if the list is empty.
    #[must_use]
    #[unstable(feature = "linked_list_cursors", issue = "58533")]
    #[rustc_confusables("last")]
    pub fn back(&self) -> Option<&T> {
        self.list.back()
    }

    /// Provides a mutable reference to back element of the cursor's parent
    /// list, or `None` if the list is empty.
    ///
    /// # Examples
    /// Building and mutating a list with a cursor, then getting the back element:
    /// ```
    /// #![feature(linked_list_cursors)]
    /// use std::collections::LinkedList;
    /// let mut dl = LinkedList::new();
    /// dl.push_front(3);
    /// dl.push_front(2);
    /// dl.push_front(1);
    /// let mut cursor = dl.cursor_front_mut();
    /// *cursor.current().unwrap() = 99;
    /// *cursor.back_mut().unwrap() = 0;
    /// let mut contents = dl.into_iter();
    /// assert_eq!(contents.next(), Some(99));
    /// assert_eq!(contents.next(), Some(2));
    /// assert_eq!(contents.next(), Some(0));
    /// assert_eq!(contents.next(), None);
    /// ```
    #[must_use]
    #[unstable(feature = "linked_list_cursors", issue = "58533")]
    pub fn back_mut(&mut self) -> Option<&mut T> {
        self.list.back_mut()
    }
}

/// An iterator produced by calling `extract_if` on LinkedList.
#[unstable(feature = "extract_if", reason = "recently added", issue = "43244")]
#[must_use = "iterators are lazy and do nothing unless consumed"]
pub struct ExtractIf<
    'a,
    T: 'a,
    F: 'a,
    #[unstable(feature = "allocator_api", issue = "32838")] A: Allocator = Global,
> where
    F: FnMut(&mut T) -> bool,
{
    list: &'a mut LinkedList<T, A>,
    it: Option<NonNull<Node<T>>>,
    pred: F,
    idx: usize,
    old_len: usize,
}

#[unstable(feature = "extract_if", reason = "recently added", issue = "43244")]
impl<T, F, A: Allocator> Iterator for ExtractIf<'_, T, F, A>
where
    F: FnMut(&mut T) -> bool,
{
    type Item = T;

    fn next(&mut self) -> Option<T> {
        while let Some(mut node) = self.it {
            unsafe {
                self.it = node.as_ref().next;
                self.idx += 1;

                if (self.pred)(&mut node.as_mut().element) {
                    // `unlink_node` is okay with aliasing `element` references.
                    self.list.unlink_node(node);
                    return Some(Box::from_raw_in(node.as_ptr(), &self.list.alloc).element);
                }
            }
        }

        None
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (0, Some(self.old_len - self.idx))
    }
}

#[unstable(feature = "extract_if", reason = "recently added", issue = "43244")]
impl<T: fmt::Debug, F> fmt::Debug for ExtractIf<'_, T, F>
where
    F: FnMut(&mut T) -> bool,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("ExtractIf").field(&self.list).finish()
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<T, A: Allocator> Iterator for IntoIter<T, A> {
    type Item = T;

    #[inline]
    fn next(&mut self) -> Option<T> {
        self.list.pop_front()
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.list.len, Some(self.list.len))
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<T, A: Allocator> DoubleEndedIterator for IntoIter<T, A> {
    #[inline]
    fn next_back(&mut self) -> Option<T> {
        self.list.pop_back()
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<T, A: Allocator> ExactSizeIterator for IntoIter<T, A> {}

#[stable(feature = "fused", since = "1.26.0")]
impl<T, A: Allocator> FusedIterator for IntoIter<T, A> {}

#[stable(feature = "default_iters", since = "1.70.0")]
impl<T> Default for IntoIter<T> {
    /// Creates an empty `linked_list::IntoIter`.
    ///
    /// ```
    /// # use std::collections::linked_list;
    /// let iter: linked_list::IntoIter<u8> = Default::default();
    /// assert_eq!(iter.len(), 0);
    /// ```
    fn default() -> Self {
        LinkedList::new().into_iter()
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<T> FromIterator<T> for LinkedList<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let mut list = Self::new();
        list.extend(iter);
        list
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<T, A: Allocator> IntoIterator for LinkedList<T, A> {
    type Item = T;
    type IntoIter = IntoIter<T, A>;

    /// Consumes the list into an iterator yielding elements by value.
    #[inline]
    fn into_iter(self) -> IntoIter<T, A> {
        IntoIter { list: self }
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<'a, T, A: Allocator> IntoIterator for &'a LinkedList<T, A> {
    type Item = &'a T;
    type IntoIter = Iter<'a, T>;

    fn into_iter(self) -> Iter<'a, T> {
        self.iter()
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<'a, T, A: Allocator> IntoIterator for &'a mut LinkedList<T, A> {
    type Item = &'a mut T;
    type IntoIter = IterMut<'a, T>;

    fn into_iter(self) -> IterMut<'a, T> {
        self.iter_mut()
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<T, A: Allocator> Extend<T> for LinkedList<T, A> {
    fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        <Self as SpecExtend<I>>::spec_extend(self, iter);
    }

    #[inline]
    fn extend_one(&mut self, elem: T) {
        self.push_back(elem);
    }
}

impl<I: IntoIterator, A: Allocator> SpecExtend<I> for LinkedList<I::Item, A> {
    default fn spec_extend(&mut self, iter: I) {
        iter.into_iter().for_each(move |elt| self.push_back(elt));
    }
}

impl<T> SpecExtend<LinkedList<T>> for LinkedList<T> {
    fn spec_extend(&mut self, ref mut other: LinkedList<T>) {
        self.append(other);
    }
}

#[stable(feature = "extend_ref", since = "1.2.0")]
impl<'a, T: 'a + Copy, A: Allocator> Extend<&'a T> for LinkedList<T, A> {
    fn extend<I: IntoIterator<Item = &'a T>>(&mut self, iter: I) {
        self.extend(iter.into_iter().cloned());
    }

    #[inline]
    fn extend_one(&mut self, &elem: &'a T) {
        self.push_back(elem);
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<T: PartialEq, A: Allocator> PartialEq for LinkedList<T, A> {
    fn eq(&self, other: &Self) -> bool {
        self.len() == other.len() && self.iter().eq(other)
    }

    fn ne(&self, other: &Self) -> bool {
        self.len() != other.len() || self.iter().ne(other)
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<T: Eq, A: Allocator> Eq for LinkedList<T, A> {}

#[stable(feature = "rust1", since = "1.0.0")]
impl<T: PartialOrd, A: Allocator> PartialOrd for LinkedList<T, A> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.iter().partial_cmp(other)
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<T: Ord, A: Allocator> Ord for LinkedList<T, A> {
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        self.iter().cmp(other)
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<T: Clone, A: Allocator + Clone> Clone for LinkedList<T, A> {
    fn clone(&self) -> Self {
        let mut list = Self::new_in(self.alloc.clone());
        list.extend(self.iter().cloned());
        list
    }

    /// Overwrites the contents of `self` with a clone of the contents of `source`.
    ///
    /// This method is preferred over simply assigning `source.clone()` to `self`,
    /// as it avoids reallocation of the nodes of the linked list. Additionally,
    /// if the element type `T` overrides `clone_from()`, this will reuse the
    /// resources of `self`'s elements as well.
    fn clone_from(&mut self, source: &Self) {
        let mut source_iter = source.iter();
        if self.len() > source.len() {
            self.split_off(source.len());
        }
        for (elem, source_elem) in self.iter_mut().zip(&mut source_iter) {
            elem.clone_from(source_elem);
        }
        if !source_iter.is_empty() {
            self.extend(source_iter.cloned());
        }
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<T: fmt::Debug, A: Allocator> fmt::Debug for LinkedList<T, A> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self).finish()
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<T: Hash, A: Allocator> Hash for LinkedList<T, A> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        state.write_length_prefix(self.len());
        for elt in self {
            elt.hash(state);
        }
    }
}

#[stable(feature = "std_collections_from_array", since = "1.56.0")]
impl<T, const N: usize> From<[T; N]> for LinkedList<T> {
    /// Converts a `[T; N]` into a `LinkedList<T>`.
    ///
    /// ```
    /// use std::collections::LinkedList;
    ///
    /// let list1 = LinkedList::from([1, 2, 3, 4]);
    /// let list2: LinkedList<_> = [1, 2, 3, 4].into();
    /// assert_eq!(list1, list2);
    /// ```
    fn from(arr: [T; N]) -> Self {
        Self::from_iter(arr)
    }
}

// Ensure that `LinkedList` and its read-only iterators are covariant in their type parameters.
#[allow(dead_code)]
fn assert_covariance() {
    fn a<'a>(x: LinkedList<&'static str>) -> LinkedList<&'a str> {
        x
    }
    fn b<'i, 'a>(x: Iter<'i, &'static str>) -> Iter<'i, &'a str> {
        x
    }
    fn c<'a>(x: IntoIter<&'static str>) -> IntoIter<&'a str> {
        x
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
unsafe impl<T: Send, A: Allocator + Send> Send for LinkedList<T, A> {}

#[stable(feature = "rust1", since = "1.0.0")]
unsafe impl<T: Sync, A: Allocator + Sync> Sync for LinkedList<T, A> {}

#[stable(feature = "rust1", since = "1.0.0")]
unsafe impl<T: Sync> Send for Iter<'_, T> {}

#[stable(feature = "rust1", since = "1.0.0")]
unsafe impl<T: Sync> Sync for Iter<'_, T> {}

#[stable(feature = "rust1", since = "1.0.0")]
unsafe impl<T: Send> Send for IterMut<'_, T> {}

#[stable(feature = "rust1", since = "1.0.0")]
unsafe impl<T: Sync> Sync for IterMut<'_, T> {}

#[unstable(feature = "linked_list_cursors", issue = "58533")]
unsafe impl<T: Sync, A: Allocator + Sync> Send for Cursor<'_, T, A> {}

#[unstable(feature = "linked_list_cursors", issue = "58533")]
unsafe impl<T: Sync, A: Allocator + Sync> Sync for Cursor<'_, T, A> {}

#[unstable(feature = "linked_list_cursors", issue = "58533")]
unsafe impl<T: Send, A: Allocator + Send> Send for CursorMut<'_, T, A> {}

#[unstable(feature = "linked_list_cursors", issue = "58533")]
unsafe impl<T: Sync, A: Allocator + Sync> Sync for CursorMut<'_, T, A> {}
