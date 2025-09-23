// verifast_options{ignore_unwind_paths}

use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

unsafe fn assert(b: bool)
//@ req b;
//@ ens true;
{
}

struct Node<T> {
    prev: *mut Node<T>,
    value: T,
    next: *mut Node<T>,
}

/*@

pred Nodes<T>(n: *Node<T>, prev: *Node<T>, last: *Node<T>, next: *Node<T>; elems: list<T>) =
    if n == next {
        elems == [] &*& last == prev
    } else {
        alloc_block_Node(n) &*&
        (*n).prev |-> prev &*&
        (*n).value |-> ?value &*&
        (*n).next |-> ?next0 &*&
        Nodes(next0, n, last, next, ?elems0) &*&
        elems == cons(value, elems0)
    };

lem Nodes_split_last<T>(n: *Node<T>)
    req Nodes(n, ?prev, ?last, ?next, ?elems) &*& 1 <= length(elems);
    ens
        Nodes(n, prev, ?last1, last, take(length(elems) - 1, elems)) &*&
        alloc_block_Node(last) &*&
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

lem Nodes_join_last<T>(n: *Node<T>)
    req
        Nodes(n, ?prev, ?last1, ?last, ?elems1) &*&
        alloc_block_Node(last) &*&
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

struct Deque<T> {
    sentinel: *mut Node<T>,
    size: i32,
}

/*@

pred Deque<T>(deque: *Deque<T>; elems: list<T>) =
    alloc_block_Deque(deque) &*&
    (*deque).sentinel |-> ?sentinel &*&
    alloc_block_Node(sentinel) &*&
    (*sentinel).prev |-> ?last &*&
    (*sentinel).value |-> _ &*&
    (*sentinel).next |-> ?first &*&
    Nodes(first, sentinel, last, sentinel, elems) &*&
    (*deque).size |-> length(elems);

@*/

impl<T> Deque<T> {
    unsafe fn new() -> *mut Deque<T>
    //@ req true;
    //@ ens Deque(result, []);
    {
        let deque = alloc(Layout::new::<Deque<T>>()) as *mut Deque<T>;
        if deque.is_null() {
            handle_alloc_error(Layout::new::<Deque<T>>());
        }
        let sentinel = alloc(Layout::new::<Node<T>>()) as *mut Node<T>;
        if sentinel.is_null() {
            handle_alloc_error(Layout::new::<Node<T>>());
        }
        (*sentinel).prev = sentinel;
        (*sentinel).next = sentinel;
        (*deque).size = 0;
        (*deque).sentinel = sentinel;
        return deque;
    }

    unsafe fn get_size(deque: *mut Deque<T>) -> i32
    //@ req Deque(deque, ?elems);
    //@ ens Deque(deque, elems) &*& result == length(elems);
    {
        return (*deque).size;
    }

    unsafe fn push_front(deque: *mut Deque<T>, value: T)
    //@ req Deque(deque, ?elems) &*& length(elems) < 0x7fffffff;
    //@ ens Deque(deque, cons(value, elems));
    {
        let new_node = alloc(Layout::new::<Node<T>>()) as *mut Node<T>;
        if new_node.is_null() {
            handle_alloc_error(Layout::new::<Node<T>>());
        }
        (*new_node).prev = (*deque).sentinel;
        std::ptr::write(&raw mut (*new_node).value, value);
        //@ close Node_value(new_node, _);
        //@ let sentinel = (*deque).sentinel;
        //@ let first = (*sentinel).next;
        (*new_node).next = (*(*deque).sentinel).next;
        (*(*new_node).prev).next = new_node;
        //@ open Nodes(first, sentinel, ?last, sentinel, elems);
        (*(*new_node).next).prev = new_node;
        (*deque).size += 1;
    }

    unsafe fn push_back(deque: *mut Deque<T>, value: T)
    //@ req Deque(deque, ?elems) &*& length(elems) < 0x7fffffff;
    //@ ens Deque(deque, append(elems, [value]));
    {
        let new_node = alloc(Layout::new::<Node<T>>()) as *mut Node<T>;
        if new_node.is_null() {
            handle_alloc_error(Layout::new::<Node<T>>());
        }
        //@ let sentinel = (*deque).sentinel;
        (*new_node).prev = (*(*deque).sentinel).prev;
        std::ptr::write(&raw mut (*new_node).value, value);
        //@ close Node_value(new_node, _);
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

    unsafe fn pop_front(deque: *mut Deque<T>) -> T
    //@ req Deque(deque, cons(?elem, ?elems));
    //@ ens Deque(deque, elems) &*& result == elem;
    {
        let node = (*(*deque).sentinel).next;
        //@ open Nodes(_, _, _, _, _);
        //@ open Node_value(node, _);
        let result = std::ptr::read(&raw mut (*node).value);
        //@ close Node_value(node, _);
        (*(*node).prev).next = (*node).next;
        //@ open Nodes(_, _, _, _, _);
        (*(*node).next).prev = (*node).prev;
        dealloc(node as *mut u8, Layout::new::<Node<T>>());
        (*deque).size -= 1;
        return result;
    }

    unsafe fn pop_back(deque: *mut Deque<T>) -> T
    //@ req Deque(deque, ?elems) &*& 1 <= length(elems);
    //@ ens Deque(deque, take(length(elems) - 1, elems)) &*& result == nth(length(elems) - 1, elems);
    {
        //@ let sentinel = (*deque).sentinel;
        //@ let first = (*sentinel).next;
        //@ Nodes_split_last(first);
        let node = (*(*deque).sentinel).prev;
        //@ open Node_value(node, _);
        let result = std::ptr::read(&raw const (*node).value);
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
        dealloc(node as *mut u8, Layout::new::<Node<T>>());
        (*deque).size -= 1;
        /*@
        if 2 <= length(elems) {
            Nodes_join_last(first);
        }
        @*/
        return result;
    }

    unsafe fn dispose(deque: *mut Deque<T>)
    //@ req Deque(deque, []);
    //@ ens true;
    {
        dealloc((*deque).sentinel as *mut u8, Layout::new::<Node<T>>());
        dealloc(deque as *mut u8, Layout::new::<Deque<T>>());
        //@ open Nodes(_, _, _, _, _);
    }

    unsafe fn swap(d: *mut Deque<T>, d1: *mut Deque<T>)
    //@ req Deque(d, ?elems) &*& Deque(d1, ?elems1);
    //@ ens Deque(d, elems1) &*& Deque(d1, elems);
    {
        let temp_sen = (*d).sentinel;
        let temp_sz = (*d).size;
        (*d).sentinel = (*d1).sentinel;
        (*d).size = (*d1).size;
        (*d1).sentinel = temp_sen;
        (*d1).size = temp_sz;
    }
}

fn main() {
    unsafe {
        let deque = Deque::<i32>::new();
        Deque::<i32>::push_back(deque, 10);
        Deque::<i32>::push_front(deque, -10);
        Deque::<i32>::push_back(deque, 20);
        Deque::<i32>::push_front(deque, -20);
        assert(Deque::<i32>::get_size(deque) == 4);
        assert(Deque::<i32>::pop_back(deque) == 20);
        assert(Deque::<i32>::pop_back(deque) == 10);
        assert(Deque::<i32>::pop_front(deque) == -20);
        assert(Deque::<i32>::pop_front(deque) == -10);
        Deque::<i32>::dispose(deque);
    }
}
