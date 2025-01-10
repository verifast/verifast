// verifast_options{ignore_ref_creation}

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

struct Node<T> {
    prev: *mut Node<T>,
    value: T,
    next: *mut Node<T>,
}

/*@

pred Nodes<T>(n: *Node<T>, prev: *Node<T>, last: *Node<T>, next: *Node<T>; nodes: list<*Node<T>>) =
    if n == next {
        nodes == [] &*& last == prev
    } else {
        std::alloc::alloc_block(n as *u8, std::alloc::Layout::new_::<Node<T>>()) &*& struct_Node_padding(n) &*&
        (*n).prev |-> prev &*&
        (*n).next |-> ?next0 &*&
        Nodes(next0, n, last, next, ?nodes0) &*&
        nodes == cons(n, nodes0)
    };

lem Nodes_split_last<T>(n: *Node<T>)
    req Nodes(n, ?prev, ?last, ?next, ?nodes) &*& 1 <= length(nodes);
    ens
        Nodes(n, prev, ?last1, last, take(length(nodes) - 1, nodes)) &*&
        std::alloc::alloc_block(last as *u8, std::alloc::Layout::new_::<Node<T>>()) &*& struct_Node_padding(last) &*&
        (*last).prev |-> last1 &*&
        (*last).next |-> next &*&
        append(take(length(nodes) - 1, nodes), [last]) == nodes;
{
    open Nodes(n, prev, last, next, nodes);
    let next0 = (*n).next;
    if length(nodes) == 1 {
        open Nodes(_, _, _, _, _);
        close Nodes(n, prev, prev, n, []);
    } else {
        Nodes_split_last((*n).next);
        assert Nodes(next0, n, ?last1, last, _);
        close Nodes(n, prev, last1, last, _);
    }
}

lem Nodes_join_last<T>(n: *Node<T>)
    req
        Nodes(n, ?prev, ?last1, ?last, ?nodes1) &*&
        std::alloc::alloc_block(last as *u8, std::alloc::Layout::new_::<Node<T>>()) &*& struct_Node_padding(last) &*&
        (*last).prev |-> last1 &*&
        (*last).next |-> ?next &*& (*next).next |-> ?nextNext;
    ens
        Nodes(n, prev, last, next, append(nodes1, [last])) &*& (*next).next |-> nextNext;
{
    open Nodes(n, prev, last1, last, nodes1);
    let next0 = (*n).next;
    if 1 <= length(nodes1) {
        Nodes_join_last(next0);
    }
}

@*/

pub struct Deque<T> {
    sentinel: *mut Node<T>,
    size: i32,
}

/*

VeriFast generates

pred_ctor Deque_full_borrow_content<T>(t: thread_id_t, deque: *Deque<T>)() =
    (*deque).sentinel |-> ?sentinel &*& (*deque).size |-> ?size &*& Deque_own(t, sentinel, size);

*/

/*@

pred Deque__<T>(sentinel: *Node<T>; nodes: list<*Node<T>>) =
    std::alloc::alloc_block(sentinel as *u8, std::alloc::Layout::new_::<Node<T>>()) &*& struct_Node_padding(sentinel) &*&
    (*sentinel).prev |-> ?last &*&
    (*sentinel).value |-> _ &*&
    (*sentinel).next |-> ?first &*&
    Nodes(first, sentinel, last, sentinel, nodes);

pred_ctor elem_points_to<T>()(node: *Node<T>; value: T) = (*node).value |-> value;

pred Deque_<T>(sentinel: *Node<T>; elems: list<T>) =
    Deque__(sentinel, ?nodes) &*& foreachp2(nodes, elem_points_to::<T>, elems);

pred_ctor elem_own<T>(t: thread_id_t)(elem: T) =
    <T>.own(t, elem);

pred<T> <Deque<T>>.own(t, deque) =
    Deque_(deque.sentinel, ?elems) &*& deque.size == length(elems) &*& foreach(elems, elem_own::<T>(t));

pred Deque<T>(deque: *Deque<T>, elems: list<T>) =
    (*deque).sentinel |-> ?sentinel &*& (*deque).size |-> ?size &*& Deque_(sentinel, elems) &*& size == length(elems);

pred_ctor Deque_frac_borrow_content<T>(nodes: list<*Node<T>>, t: thread_id_t, l: *Deque<T>)(;) =
    (*l).sentinel |-> ?sentinel &*& (*l).size |-> ?size &*&
    Deque__(sentinel, nodes) &*& size == length(nodes) &*&
    struct_Deque_padding(l);

pred_ctor elem_share<T>(k: lifetime_t, t: thread_id_t)(l: *Node<T>) =
    [_](<T>.share)(k, t, &(*l).value);

pred<T> <Deque<T>>.share(k, t, l) =
    exists::<list<*Node<T>>>(?nodes) &*&
    [_]frac_borrow(k, Deque_frac_borrow_content(nodes, t, l)) &*&
    foreach(nodes, elem_share::<T>(k, t));

pred_ctor elems_fbc<T>(t: thread_id_t, nodes: list<*Node<T>>)() =
    foreachp2(nodes, elem_points_to::<T>, ?elems) &*& foreach(elems, elem_own::<T>(t));

lem elems_share_full<T>(t: thread_id_t, nodes: list<*Node<T>>)
    req type_interp::<T>() &*& atomic_mask(Nlft) &*& full_borrow(?k, elems_fbc(t, nodes)) &*& [?q]lifetime_token(k);
    ens type_interp::<T>() &*& atomic_mask(Nlft) &*& foreach(nodes, elem_share::<T>(k, t)) &*& [q]lifetime_token(k);
{
    match nodes {
        nil => {
            leak full_borrow(_, _);
            close foreach(nodes, elem_share::<T>(k, t));
        }
        cons(node, nodes0) => {
            let klong = open_full_borrow_strong_m(k, elems_fbc(t, nodes), q);
            produce_lem_ptr_chunk full_borrow_convert_strong(True, sep(<T>.full_borrow_content(t, &(*node).value), elems_fbc(t, nodes0)), klong, elems_fbc(t, nodes))() {
                open sep(<T>.full_borrow_content(t, &(*node).value), elems_fbc(t, nodes0))();
                open_full_borrow_content::<T>(t, &(*node).value);
                open elems_fbc::<T>(t, nodes0)();
                assert foreach(?elems0, _);
                close Node_value(node, ?elem);
                close elem_points_to::<T>()(node, _);
                close foreachp2(nodes, elem_points_to::<T>(), _);
                close elem_own::<T>(t)(elem);
                close foreach(cons(elem, elems0), elem_own::<T>(t));
                close elems_fbc::<T>(t, nodes)();
            } {
                open elems_fbc::<T>(t, nodes)();
                open foreachp2(_, _, ?elems);
                open elem_points_to::<T>()(node, ?elem);
                open Node_value(node, _);
                open foreach(_, _);
                open elem_own::<T>(t)(elem);
                close_full_borrow_content(t, &(*node).value);
                close elems_fbc::<T>(t, nodes0)();
                close sep(<T>.full_borrow_content(t, &(*node).value), elems_fbc(t, nodes0))();
                close_full_borrow_strong_m(klong, elems_fbc(t, nodes), sep(<T>.full_borrow_content(t, &(*node).value), elems_fbc(t, nodes0)));
            }
            full_borrow_mono(klong, k, sep(<T>.full_borrow_content(t, &(*node).value), elems_fbc(t, nodes0)));
            full_borrow_split_m(k, <T>.full_borrow_content(t, &(*node).value), elems_fbc(t, nodes0));
            share_full_borrow_m::<T>(k, t, &(*node).value);
            elems_share_full(t, nodes0);
            close elem_share::<T>(k, t)(node);
            close foreach(nodes, elem_share::<T>(k, t));
        }
    }
}

lem Deque_share_full<T>(k: lifetime_t, t: thread_id_t, l: *Deque<T>)
    req type_interp::<T>() &*& atomic_mask(Nlft) &*& full_borrow(k, Deque_full_borrow_content(t, l)) &*& [?q]lifetime_token(k);
    ens type_interp::<T>() &*& atomic_mask(Nlft) &*& [_]Deque_share(k, t, l) &*& [q]lifetime_token(k);
{
    let klong = open_full_borrow_strong_m(k, Deque_full_borrow_content(t, l), q);
    open Deque_full_borrow_content::<T>(t, l)();
    open Deque_own::<T>()(t, ?deque);
    open Deque_(deque.sentinel, _);
    assert Deque__(deque.sentinel, ?nodes);
    produce_lem_ptr_chunk full_borrow_convert_strong(True, sep(Deque_frac_borrow_content(nodes, t, l), elems_fbc(t, nodes)), klong, Deque_full_borrow_content(t, l))() {
        open sep(Deque_frac_borrow_content(nodes, t, l), elems_fbc(t, nodes))();
        open Deque_frac_borrow_content::<T>(nodes, t, l)();
        assert Deque__::<T>(?sentinel1, nodes);
        open elems_fbc::<T>(t, nodes)();
        close Deque_own::<T>(t, Deque::<T> { sentinel: sentinel1, size: length(nodes) });
        close Deque_full_borrow_content::<T>(t, l)();
    } {
        close Deque_frac_borrow_content::<T>(nodes, t, l)();
        close elems_fbc::<T>(t, nodes)();
        close sep(Deque_frac_borrow_content(nodes, t, l), elems_fbc(t, nodes))();
        close_full_borrow_strong_m(klong, Deque_full_borrow_content(t, l), sep(Deque_frac_borrow_content(nodes, t, l), elems_fbc(t, nodes)));
    }
    full_borrow_mono(klong, k, sep(Deque_frac_borrow_content(nodes, t, l), elems_fbc(t, nodes)));
    full_borrow_split_m(k, Deque_frac_borrow_content(nodes, t, l), elems_fbc(t, nodes));
    full_borrow_into_frac_m(k, Deque_frac_borrow_content(nodes, t, l));
    elems_share_full(t, nodes);
    close exists(nodes);
    close Deque_share::<T>()(k, t, l);
    leak Deque_share::<T>()(k, t, l);
}

lem foreach_elem_share_mono<T>(k: lifetime_t, k1: lifetime_t, t: thread_id_t)
    req [?q]foreach(?nodes, elem_share::<T>(k, t)) &*& type_interp::<T>() &*& lifetime_inclusion(k1, k) == true;
    ens type_interp::<T>() &*& [q]foreach(nodes, elem_share::<T>(k1, t));
{
    open foreach(nodes, elem_share::<T>(k, t));
    match nodes {
        nil => {}
        cons(node, nodes0) => {
            open elem_share::<T>(k, t)(node);
            share_mono(k, k1, t, &(*node).value);
            close [q]elem_share::<T>(k1, t)(node);
            foreach_elem_share_mono::<T>(k, k1, t);
        }
    }
    close [q]foreach(nodes, elem_share::<T>(k1, t));
}

lem Deque_share_mono<T>(k: lifetime_t, k1: lifetime_t, t: thread_id_t, l: *Deque<T>)
    req type_interp::<T>() &*& lifetime_inclusion(k1, k) == true &*& [_]Deque_share(k, t, l);
    ens type_interp::<T>() &*& [_]Deque_share(k1, t, l);
{
    open [?q]Deque_share::<T>(k, t, l);
    assert [_]exists(?nodes);
    frac_borrow_mono(k, k1, Deque_frac_borrow_content(nodes, t, l));
    foreach_elem_share_mono::<T>(k, k1, t);
    close [q]exists(nodes);
    close [q]Deque_share::<T>()(k1, t, l);
}

lem init_ref_Deque<T>(p: *Deque<T>)
    req type_interp::<T>() &*& atomic_mask(Nlft) &*& ref_init_perm(p, ?x) &*& [_]Deque_share::<T>(?k, ?t, x) &*& [?q]lifetime_token(k);
    ens type_interp::<T>() &*& atomic_mask(Nlft) &*& [q]lifetime_token(k) &*& [_]Deque_share::<T>(k, t, p) &*& [_]frac_borrow(k, ref_initialized_(p));
{
    assume(false);
}

@*/

impl<T> Deque<T> {

    pub fn new() -> Deque<T> {
        unsafe {
            let sentinel = std::alloc::alloc(std::alloc::Layout::new::<Node<T>>()) as *mut Node<T>;
            if sentinel.is_null() {
                std::alloc::handle_alloc_error(std::alloc::Layout::new::<Node<T>>());
            }
            //@ close_struct(sentinel);
            (*sentinel).prev = sentinel;
            (*sentinel).next = sentinel;
            //@ close foreach(nil, elem_own::<T>(_t));
            //@ close Deque_own::<T>()(_t, Deque::<T> { sentinel, size: 0 });
            Deque { sentinel, size: 0 }
        }
    }

    pub fn get_size<'a>(&'a self) -> i32 {
        //@ open Deque_share::<T>()('a, _t, self);
        //@ assert [?q]exists(?nodes);
        //@ open_frac_borrow('a, Deque_frac_borrow_content(nodes, _t, self), _q_a);
        //@ open [?qf]Deque_frac_borrow_content::<T>(nodes, _t, self)();
        let size = (*self).size;
        //@ close [qf]Deque_frac_borrow_content::<T>(nodes, _t, self)();
        //@ close_frac_borrow(qf, Deque_frac_borrow_content(nodes, _t, self));
        return size;
    }

    unsafe fn unsafe_push_front(deque: *mut Deque<T>, value: T)
        //@ req Deque(deque, ?elems) &*& length(elems) < 0x7fffffff;
        //@ ens Deque(deque, cons(value, elems));
    {
        let new_node = std::alloc::alloc(std::alloc::Layout::new::<Node<T>>()) as *mut Node<T>;
        if new_node.is_null() {
            std::alloc::handle_alloc_error(std::alloc::Layout::new::<Node<T>>());
        }
        //@ close_struct(new_node);
        //@ open Deque(_, _);
        (*new_node).prev = (*deque).sentinel;
        std::ptr::write(&raw mut (*new_node).value, value);
        //@ let sentinel = (*deque).sentinel;
        //@ let first = (*sentinel).next;
        (*new_node).next = (*(*deque).sentinel).next;
        (*(*new_node).prev).next = new_node;
        //@ open Nodes(first, sentinel, ?last, sentinel, ?nodes);
        (*(*new_node).next).prev = new_node;
        (*deque).size += 1;
        //@ close Node_value(new_node, value);
        //@ close elem_points_to::<T>(new_node, value);
        //@ close foreachp2(cons(new_node, nodes), elem_points_to::<T>, cons(value, elems));
        //@ close Deque_(sentinel, cons(value, elems));
        //@ close Deque(deque, cons(value, elems));
    }

    pub fn push_front(&mut self, value: T) {
        //@ open Deque_own::<T>()(_t, ?deque);
        if (*self).size < 0x7fffffff {
            unsafe {
                //@ close Deque(self, ?elems);
                Self::unsafe_push_front(self, value);
                //@ open Deque(self, _);
            }
        } else {
            std::process::abort();
        }
        //@ let sentinel = (*self).sentinel;
        //@ close elem_own::<T>(_t)(value);
        //@ close foreach(cons(value, elems), elem_own::<T>(_t));
        //@ close Deque_own::<T>()(_t, Deque::<T> { sentinel, size: deque.size + 1 });
    }

    unsafe fn unsafe_push_back(deque: *mut Deque<T>, value: T)
        //@ req Deque(deque, ?elems) &*& length(elems) < 0x7fffffff;
        //@ ens Deque(deque, append(elems, [value]));
    {
        let new_node = std::alloc::alloc(std::alloc::Layout::new::<Node<T>>()) as *mut Node<T>;
        if new_node.is_null() {
            std::alloc::handle_alloc_error(std::alloc::Layout::new::<Node<T>>());
        }
        //@ close_struct(new_node);
        //@ open Deque(_, _);
        //@ let sentinel = (*deque).sentinel;
        (*new_node).prev = (*(*deque).sentinel).prev;
        std::ptr::write(&raw mut (*new_node).value, value);
        (*new_node).next = (*deque).sentinel;
        //@ assert Deque__(sentinel, ?nodes);
        /*@
        if length(nodes) > 0 {
            Nodes_split_last((*sentinel).next);
        } else {
            open Nodes(?first, sentinel, ?last, sentinel, nodes);
            open foreachp2(_, _, _);
        }
        @*/
        (*(*new_node).prev).next = new_node;
        (*(*new_node).next).prev = new_node;
        (*deque).size += 1;
        /*@
        if length(nodes) > 0 {
            Nodes_join_last((*sentinel).next);
            append_take_drop_n(nodes, length(nodes) - 1);
            drop_n_plus_one(length(nodes) - 1, nodes);
        } else {
            close Nodes(new_node, sentinel, sentinel, new_node, []);
        }
        @*/
        //@ Nodes_join_last((*sentinel).next);
        //@ close foreachp2([], elem_points_to::<T>(), []);
        //@ close Node_value(new_node, value);
        //@ close elem_points_to::<T>(new_node, value);
        //@ close foreachp2([new_node], elem_points_to::<T>(), [value]);
        //@ foreachp2_append(nodes, [new_node], elem_points_to::<T>());
        //@ close Deque(deque, append(elems, [value]));
    }

    pub fn push_back(&mut self, value: T) {
        //@ open Deque_own::<T>()(_t, ?deque);
        if (*self).size < 0x7fffffff {
            unsafe {
                //@ close Deque(self, ?elems);
                Self::unsafe_push_back(self, value);
                //@ open Deque(self, _);
            }
        } else {
            std::process::abort()
        }
        //@ let sentinel = (*self).sentinel;
        //@ close elem_own::<T>(_t)(value);
        //@ close foreach([], elem_own::<T>(_t));
        //@ close foreach([value], elem_own::<T>(_t));
        //@ foreach_append(elems, [value]);
        //@ close Deque_own::<T>()(_t, Deque::<T> { sentinel, size: deque.size + 1 });
    }

    unsafe fn unsafe_pop_front(deque: *mut Deque<T>) -> T
        //@ req Deque(deque, cons(?elem, ?elems));
        //@ ens Deque(deque, elems) &*& result == elem;
    {
        //@ open Deque(deque, _);
        let node = (*(*deque).sentinel).next;
        //@ open Nodes(_, _, _, _, _);
        //@ open foreachp2(_, _, _);
        //@ open elem_points_to::<T>()(node, ?value);
        //@ open Node_value(node, _);
        let result = std::ptr::read(&(*node).value);
        //@ close Node_value(node, _);
        (*(*node).prev).next = (*node).next;
        //@ open Nodes(_, _, _, _, _);
        (*(*node).next).prev = (*node).prev;
        //@ open_struct(node);
        std::alloc::dealloc(node as *mut u8, std::alloc::Layout::new::<Node<T>>());
        (*deque).size -= 1;
        //@ close Deque(deque, elems);
        result
    }

    pub fn pop_front(&mut self) -> T
        //@ req thread_token(?_t) &*& *self |-> ?deque &*& Deque_own::<T>(_t, deque);
        //@ ens thread_token(_t) &*& *self |-> ?deque1 &*& Deque_own::<T>(_t, deque1) &*& <T>.own(_t, result);
    {
        //@ open Deque_own::<T>()(_t, deque);
        if (*self).size == 0 {
            std::process::abort();
        }
        unsafe {
            //@ close Deque(self, ?elems);
            let result = Self::unsafe_pop_front(self);
            //@ open Deque(self, _);
            //@ let sentinel = (*self).sentinel;
            //@ open foreach(_, _);
            //@ open elem_own::<T>(_t)(result);
            //@ close Deque_own::<T>()(_t, Deque::<T> { sentinel, size: deque.size - 1 });
            return result;
        }
    }

    unsafe fn unsafe_pop_back(deque: *mut Deque<T>) -> T
        //@ req Deque(deque, ?elems) &*& 1 <= length(elems);
        //@ ens Deque(deque, take(length(elems) - 1, elems)) &*& result == nth(length(elems) - 1, elems);
    {
        //@ open Deque(deque, _);
        //@ let sentinel = (*deque).sentinel;
        //@ let first = (*sentinel).next;
        //@ assert Deque__(sentinel, ?nodes);
        //@ Nodes_split_last(first);
        let node = (*(*deque).sentinel).prev;
        //@ foreachp2_unappend(take(length(elems) - 1, nodes), [node], elem_points_to::<T>());
        //@ open foreachp2([node], _, _);
        //@ open elem_points_to::<T>(node, ?value);
        //@ open Node_value(node, _);
        let result = std::ptr::read(&(*node).value);
        //@ close Node_value(node, _);
        /*@
        if 2 <= length(elems) {
            Nodes_split_last(first);
            append_take_drop_n(take(length(elems) - 1, elems), length(elems) - 2);
            drop_n_plus_one(length(elems) - 2, take(length(elems) - 1, elems));
        } else {
            open Nodes(first, sentinel, ?last1, ?last, _);
        }
        @*/
        (*(*node).prev).next = (*node).next;
        (*(*node).next).prev = (*node).prev;
        //@ open_struct(node);
        std::alloc::dealloc(node as *mut u8, std::alloc::Layout::new::<Node<T>>());
        (*deque).size -= 1;
        /*@
        if 2 <= length(elems) {
            Nodes_join_last(first);
        }
        @*/
        //@ close Deque(deque, take(length(elems) - 1, elems));
        //@ nth_drop(0, length(elems) - 1, elems);
        return result;
    }

    pub fn pop_back(&mut self) -> T {
        //@ open Deque_own::<T>()(_t, ?deque);
        if (*self).size == 0 {
            std::process::abort();
        }
        unsafe {
            //@ close Deque(self, ?elems);
            let result = Self::unsafe_pop_back(self);
            //@ open Deque(self, _);
            //@ let sentinel = (*self).sentinel;
            //@ append_take_drop_n(elems, length(elems) - 1);
            //@ foreach_unappend(take(length(elems) - 1, elems), drop(length(elems) - 1, elems), elem_own::<T>(_t));
            //@ open foreach(drop(length(elems) - 1, elems), _);
            //@ open foreach(tail(drop(length(elems) - 1, elems)), _);
            //@ nth_drop(0, length(elems) - 1, elems);
            //@ open elem_own::<T>(_t)(result);
            //@ close Deque_own::<T>()(_t, Deque::<T> { sentinel, size: deque.size - 1 });
            return result;
        }
    }

    unsafe fn dispose_nodes(first: *mut Node<T>, next: *mut Node<T>)
        //@ req thread_token(?_t) &*& Nodes(first, ?prev, ?last, next, ?nodes) &*& Node_next(next, _) &*& foreachp2(nodes, elem_points_to::<T>(), ?elems) &*& foreach(elems, elem_own::<T>(_t));
        //@ ens thread_token(_t) &*& Node_next(next, _);
    {
        //@ open Nodes(_, _, _, _, _);
        //@ open foreachp2(_, _, _);
        //@ open foreach(_, _);
        if first == next {
            return;
        }
        let first1 = (*first).next;
        //@ open elem_points_to::<T>(first, ?value);
        //@ open elem_own::<T>(_t)(value);
        //@ open Node_value(first, _);
        std::ptr::drop_in_place(&mut (*first).value);
        //@ open_struct(first);
        std::alloc::dealloc(first as *mut u8, std::alloc::Layout::new::<Node<T>>());
        Self::dispose_nodes(first1, next);
    }

}

impl<T> Drop for Deque<T> {

    fn drop<'a>(&'a mut self)
    //@ req thread_token(?_t) &*& Deque_full_borrow_content::<T>(_t, self)();
    /*@
    ens
        thread_token(_t) &*&
        (*self).sentinel |-> ?sentinel &*&
        (*self).size |-> ?size &*&
        struct_Deque_padding(self);
    @*/
    {
        unsafe {
            //@ open Deque_full_borrow_content::<T>(_t, self)();
            //@ open Deque_own::<T>()(_t, ?deque);
            Self::dispose_nodes((*(self.sentinel)).next, self.sentinel);
            //@ open_struct((*self).sentinel);
            std::alloc::dealloc(self.sentinel as *mut u8, std::alloc::Layout::new::<Node<T>>());
        }
    }

}
