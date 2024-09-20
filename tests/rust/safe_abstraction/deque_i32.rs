struct Node {
    prev: *mut Node,
    value: i32,
    next: *mut Node,
}

/*@

pred Nodes(n: *Node, prev: *Node, last: *Node, next: *Node; elems: list<i32>) =
    if n == next {
        elems == [] &*& last == prev
    } else {
        std::alloc::alloc_block(n as *u8, std::alloc::Layout::new_::<Node>()) &*& struct_Node_padding(n) &*&
        (*n).prev |-> prev &*&
        (*n).value |-> ?value &*&
        (*n).next |-> ?next0 &*&
        Nodes(next0, n, last, next, ?elems0) &*&
        elems == cons(value, elems0)
    };

lem Nodes_split_last(n: *Node)
    req Nodes(n, ?prev, ?last, ?next, ?elems) &*& 1 <= length(elems);
    ens
        Nodes(n, prev, ?last1, last, take(length(elems) - 1, elems)) &*&
        std::alloc::alloc_block(last as *u8, std::alloc::Layout::new_::<Node>()) &*& struct_Node_padding(last) &*&
        (*last).prev |-> last1 &*&
        (*last).value |-> nth(length(elems) - 1, elems) &*&
        (*last).next |-> next;
{
    open Nodes(n, prev, last, next, elems);
    let next0 = (*n).next;
    if length(elems) == 1 {
        open Nodes(_, _, _, _, _);
        close Nodes(n, prev, prev, n, []);
    } else {
        Nodes_split_last((*n).next);
        assert Nodes(next0, n, ?last1, last, _);
        close Nodes(n, prev, last1, last, _);
    }
}

lem Nodes_join_last(n: *Node)
    req
        Nodes(n, ?prev, ?last1, ?last, ?elems1) &*&
        std::alloc::alloc_block(last as *u8, std::alloc::Layout::new_::<Node>()) &*& struct_Node_padding(last) &*&
        (*last).prev |-> last1 &*&
        (*last).value |-> ?value &*&
        (*last).next |-> ?next &*& (*next).next |-> ?nextNext;
    ens
        Nodes(n, prev, last, next, append(elems1, [value])) &*& (*next).next |-> nextNext;
{
    open Nodes(n, prev, last1, last, elems1);
    let next0 = (*n).next;
    if 1 <= length(elems1) {
        Nodes_join_last(next0);
    }
}

@*/

pub struct Deque {
    sentinel: *mut Node,
    size: i32,
}

/* VeriFast generates
pred Deque_full_borrow_content(t: thread_id_t, deque: *Deque) =
    (*deque).sentinel |-> ?sentinel &*& (*deque).size |-> ?size &*& Deque_own(t, sentinel, size);
*/

/*@
pred Deque_(sentinel: *Node; elems: list<i32> ) =
    std::alloc::alloc_block(sentinel as *u8, std::alloc::Layout::new_::<Node>()) &*& struct_Node_padding(sentinel) &*&
    (*sentinel).prev |-> ?last &*&
    (*sentinel).value |-> _ &*&
    (*sentinel).next |-> ?first &*&
    Nodes(first, sentinel, last, sentinel, elems);

pred <Deque>.own(t, deque;) =
    Deque_(deque.sentinel, ?elems) &*& deque.size == length(elems);

pred Deque(deque: *Deque; elems: list<i32>) =
    (*deque).sentinel |-> ?sentinel &*& (*deque).size |-> ?size &*& Deque_(sentinel, elems) &*& size == length(elems);

pred_ctor Deque_frac_borrow_content(t: thread_id_t, l: *Deque)(;) =
    (*l).sentinel |-> ?sentinel &*& (*l).size |-> ?size &*& Deque_own(t, Deque { sentinel, size }) &*& struct_Deque_padding(l);
pred <Deque>.share(k, t, l) = [_]frac_borrow(k, Deque_frac_borrow_content(t, l));

// Proof obligations
lem Deque_share_mono(k: lifetime_t, k1: lifetime_t, t: thread_id_t, l: *Deque)
    req lifetime_inclusion(k1, k) == true &*& [_]Deque_share(k, t, l);
    ens [_]Deque_share(k1, t, l);
{
    open Deque_share(k, t, l);
    frac_borrow_mono(k, k1, Deque_frac_borrow_content(t, l));
    assert [?q]frac_borrow(k1, _);
    close [q]Deque_share(k1, t, l);
}

lem Deque_share_full(k: lifetime_t, t: thread_id_t, l: *Deque)
    req atomic_mask(Nlft) &*& full_borrow(k, Deque_full_borrow_content(t, l)) &*& [?q]lifetime_token(k);
    ens atomic_mask(Nlft) &*& [_]Deque_share(k, t, l) &*& [q]lifetime_token(k);
{
    produce_lem_ptr_chunk implies(Deque_full_borrow_content(t, l), Deque_frac_borrow_content(t, l))() {
        open Deque_full_borrow_content(t, l)();
    }{
        produce_lem_ptr_chunk implies(Deque_frac_borrow_content(t, l), Deque_full_borrow_content(t, l))() {
            close Deque_full_borrow_content(t, l)();
        }{
            full_borrow_implies(k, Deque_full_borrow_content(t, l), Deque_frac_borrow_content(t, l));
        }
    }
    full_borrow_into_frac_m(k, Deque_frac_borrow_content(t, l));
    assert [?q_f]frac_borrow(_, _);
    close [q_f]Deque_share(k, t, l);
}
@*/

impl Deque {
    pub fn new() -> Deque {
        unsafe {
            let sentinel = std::alloc::alloc(std::alloc::Layout::new::<Node>()) as *mut Node;
            if sentinel.is_null() {
                std::alloc::handle_alloc_error(std::alloc::Layout::new::<Node>());
            }
            //@ close_struct(sentinel);
            (*sentinel).prev = sentinel;
            (*sentinel).next = sentinel;
            //@ close Deque_own(_t, Deque { sentinel, size: 0 });
            Deque { sentinel, size: 0 }
        }
    }

    pub fn get_size<'a>(&'a self) -> i32 {
        //@ open Deque_share('a, _t, self);
        //@ open_frac_borrow('a, Deque_frac_borrow_content(_t, self), _q_a);
        let size = (*self).size;
        //@ assert [?q_p]Deque_size(self, _);
        //@ close_frac_borrow(q_p, Deque_frac_borrow_content(_t, self));
        return size;
    }

    unsafe fn unsafe_push_front(deque: *mut Deque, value: i32)
        //@ req Deque(deque, ?elems) &*& length(elems) < 0x7fffffff;
        //@ ens Deque(deque, cons(value, elems));
    {
        let new_node = std::alloc::alloc(std::alloc::Layout::new::<Node>()) as *mut Node;
        if new_node.is_null() {
            std::alloc::handle_alloc_error(std::alloc::Layout::new::<Node>());
        }
        //@ close_struct(new_node);
        (*new_node).prev = (*deque).sentinel;
        (*new_node).value = value;
        //@ let sentinel = (*deque).sentinel;
        //@ let first = (*sentinel).next;
        (*new_node).next = (*(*deque).sentinel).next;
        (*(*new_node).prev).next = new_node;
        //@ open Nodes(first, sentinel, ?last, sentinel, elems);
        (*(*new_node).next).prev = new_node;
        (*deque).size += 1;
    }

    pub fn push_front<'a>(&'a mut self, value: i32) {
        //@ open_full_borrow(_q_a, 'a, Deque_full_borrow_content(_t, self));
        //@ open Deque_full_borrow_content(_t, self)();
        if (*self).size < 0x7fffffff {
            unsafe {
                Self::unsafe_push_front(self, value);
            }
        } else {
            std::process::abort();
        }
        //@ let sentinel = (*self).sentinel;
        //@ close Deque_full_borrow_content(_t, self)();
        //@ close_full_borrow(Deque_full_borrow_content(_t, self));
        //@ leak full_borrow(_, _);
    }

    unsafe fn unsafe_push_back(deque: *mut Deque, value: i32)
        //@ req Deque(deque, ?elems) &*& length(elems) < 0x7fffffff;
        //@ ens Deque(deque, append(elems, [value]));
    {
        let new_node = std::alloc::alloc(std::alloc::Layout::new::<Node>()) as *mut Node;
        if new_node.is_null() {
            std::alloc::handle_alloc_error(std::alloc::Layout::new::<Node>());
        }
        //@ close_struct(new_node);
        //@ let sentinel = (*deque).sentinel;
        (*new_node).prev = (*(*deque).sentinel).prev;
        (*new_node).value = value;
        (*new_node).next = (*deque).sentinel;
        /*@
        if length(elems) > 0 {
            Nodes_split_last((*sentinel).next);
        } else {
            open Nodes(?first, sentinel, ?last, sentinel, elems);
        }
        @*/
        (*(*new_node).prev).next = new_node;
        (*(*new_node).next).prev = new_node;
        (*deque).size += 1;
        /*@
        if length(elems) > 0 {
            Nodes_join_last((*sentinel).next);
            append_take_drop_n(elems, length(elems) - 1);
            drop_n_plus_one(length(elems) - 1, elems);
        } else {
            close Nodes(new_node, sentinel, sentinel, new_node, []);
        }
        @*/
        //@ Nodes_join_last((*sentinel).next);
    }

    pub fn push_back<'a>(&'a mut self, value: i32) {
        //@ open_full_borrow(_q_a, 'a, Deque_full_borrow_content(_t, self));
        //@ open Deque_full_borrow_content(_t, self)();
        if (*self).size < 0x7fffffff {
            unsafe { Self::unsafe_push_back(self, value) }
        } else {
            std::process::abort()
        }
        //@ close Deque_full_borrow_content(_t, self)();
        //@ close_full_borrow(Deque_full_borrow_content(_t, self));
        //@ leak full_borrow(_, _);
    }

    unsafe fn unsafe_pop_front(deque: *mut Deque) -> i32
        //@ req Deque(deque, cons(?elem, ?elems));
        //@ ens Deque(deque, elems) &*& result == elem;
    {
        let node = (*(*deque).sentinel).next;
        //@ open Nodes(_, _, _, _, _);
        let result = (*node).value;
        (*(*node).prev).next = (*node).next;
        //@ open Nodes(_, _, _, _, _);
        (*(*node).next).prev = (*node).prev;
        //@ open_struct(node);
        std::alloc::dealloc(node as *mut u8, std::alloc::Layout::new::<Node>());
        (*deque).size -= 1;
        return result;
    }

    pub fn pop_front<'a>(&'a mut self) -> i32
        //@ req thread_token(?_t) &*& [?_q]lifetime_token(?a) &*& full_borrow(a, Deque_full_borrow_content(_t, self));
        //@ ens thread_token(_t) &*& [_q]lifetime_token(a);
    {
        //@ open_full_borrow(_q, a, Deque_full_borrow_content(_t, self));
        //@ open Deque_full_borrow_content(_t, self)();
        if (*self).size == 0 {
            std::process::abort();
        } else {
            unsafe {
                let result = Self::unsafe_pop_front(self);
                //@ close Deque_full_borrow_content(_t, self)();
                //@ close_full_borrow(Deque_full_borrow_content(_t, self));
                //@ leak full_borrow(_, _);
                return result;
            }
        }
    }

    unsafe fn unsafe_pop_back(deque: *mut Deque) -> i32
        //@ req Deque(deque, ?elems) &*& 1 <= length(elems);
        //@ ens Deque(deque, take(length(elems) - 1, elems)) &*& result == nth(length(elems) - 1, elems);
    {
        //@ let sentinel = (*deque).sentinel;
        //@ let first = (*sentinel).next;
        //@ Nodes_split_last(first);
        let node = (*(*deque).sentinel).prev;
        let result = (*node).value;
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
        std::alloc::dealloc(node as *mut u8, std::alloc::Layout::new::<Node>());
        (*deque).size -= 1;
        /*@
        if 2 <= length(elems) {
            Nodes_join_last(first);
        }
        @*/
        return result;
    }

    pub fn pop_back<'a>(&'a mut self) -> i32 {
        //@ open_full_borrow(_q_a, 'a, Deque_full_borrow_content(_t, self));
        //@ open Deque_full_borrow_content(_t, self)();
        if (*self).size == 0 {
            std::process::abort();
        } else {
            unsafe {
                let result = Self::unsafe_pop_back(self);
                //@ close Deque_full_borrow_content(_t, self)();
                //@ close_full_borrow(Deque_full_borrow_content(_t, self));
                //@ leak full_borrow(_, _);
                return result;
            }
        }
    }

    unsafe fn dispose_nodes(first: *mut Node, next: *mut Node)
        //@ req Nodes(first, ?prev, ?last, next, ?elems) &*& Node_next(next, _);
        //@ ens Node_next(next, _);
    {
        //@ open Nodes(_, _, _, _, _);
        if first == next {
            return;
        }
        let first1 = (*first).next;
        //@ open_struct(first);
        std::alloc::dealloc(first as *mut u8, std::alloc::Layout::new::<Node>());
        Self::dispose_nodes(first1, next);
    }

    pub fn swap<'a>(&'a mut self, other: &'a mut Deque) {
        //@ open_full_borrow(_q_a/2, 'a, Deque_full_borrow_content(_t, self));
        //@ open Deque_full_borrow_content(_t, self)();
        let tmp_sen = (*self).sentinel;
        let tmp_sz = (*self).size;
        //@ open_full_borrow(_q_a/2, 'a, Deque_full_borrow_content(_t, other));
        //@ open Deque_full_borrow_content(_t, other)();
        (*self).sentinel = (*other).sentinel;
        (*self).size = (*other).size;
        (*other).sentinel = tmp_sen;
        (*other).size = tmp_sz;
        //@ close Deque_full_borrow_content(_t, self)();
        //@ close_full_borrow(Deque_full_borrow_content(_t, self));
        //@ close Deque_full_borrow_content(_t, other)();
        //@ close_full_borrow(Deque_full_borrow_content(_t, other));
        //@ leak full_borrow(_, _);
        //@ leak full_borrow(_, _);
    }
}

impl Drop for Deque {

    fn drop<'a>(&'a mut self)
    //@ req thread_token(?_t) &*& Deque_full_borrow_content(_t, self)();
    /*@
    ens
        thread_token(_t) &*&
        (*self).sentinel |-> ?sentinel &*&
        (*self).size |-> ?size &*&
        struct_Deque_padding(self);
    @*/
    {
        unsafe {
            //@ open Deque_full_borrow_content(_t, self)();
            Self::dispose_nodes((*(self.sentinel)).next, self.sentinel);
            //@ open_struct((*self).sentinel);
            std::alloc::dealloc(self.sentinel as *mut u8, std::alloc::Layout::new::<Node>());
        }
    }

}
