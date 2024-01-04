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
        alloc_block(n, std::mem::size_of::<Node>()) &*& struct_Node_padding(n) &*&
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
        alloc_block(last, std::mem::size_of::<Node>()) &*& struct_Node_padding(last) &*&
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
        alloc_block(last, std::mem::size_of::<Node>()) &*& struct_Node_padding(last) &*&
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

// pred Deque_full_borrow_content(deque: *Deque) = Deque_sentinel(deque, ?sentinel) &*& deque->size |-> ?size &*& Deque_own(_

/*@
pred Deque_own(t: thread_id_t, sentinel: *Node, size: i32) =
  alloc_block(sentinel, std::mem::size_of::<Node>()) &*& struct_Node_padding(sentinel) &*&
  (*sentinel).prev |-> ?last &*&
  (*sentinel).value |-> _ &*&
  (*sentinel).next |-> ?first &*&
  Nodes(first, sentinel, last, sentinel, ?elems) &*&
  size == length(elems);

pred Deque_share(k: lifetime_t, t: thread_id_t, l: *Deque) = true;

lem Deque_share_mono(k: lifetime_t, k1: lifetime_t, t: thread_id_t, l: *Deque)
  req lifetime_inclusion(k1, k) == true &*& [_]Deque_share(k, t, l);
  ens [_]Deque_share(k1, t, l);
{
  close Deque_share(k1, t, l);
  leak Deque_share(k1, t, l);
}

lem Deque_share_full(k: lifetime_t, t: thread_id_t, l: *Deque)
  req full_borrow(k, Deque_full_borrow_content(t, l)) &*& [?q]lifetime_token(k);
  ens [_]Deque_share(k, t, l) &*& [q]lifetime_token(k);
{
  close Deque_share(k, t, l);
  leak Deque_share(k, t, l);
  leak full_borrow(_, _);
}
@*/

impl Deque {
    pub fn new() -> Deque
// req true;
    // ens Deque(result, []);
    {
        unsafe {
            let sentinel = std::alloc::alloc(std::alloc::Layout::new::<Node>()) as *mut Node;
            if sentinel.is_null() {
                std::alloc::handle_alloc_error(std::alloc::Layout::new::<Node>());
            }
            //@ close_struct(sentinel);
            (*sentinel).prev = sentinel;
            (*sentinel).next = sentinel;
            //@ close Deque_own(_t, sentinel, 0);
            Deque { sentinel, size: 0 }
        }
    }

    fn get_size<'a>(deque: &'a mut Deque) -> i32
// req Deque(deque, ?elems);
        // ens Deque(deque, elems) &*& result == length(elems);
    {
        //@ open_full_borrow(a, Deque_full_borrow_content(_t, deque));
        //@ open Deque_full_borrow_content(_t, deque)();
        let size = (*deque).size;
        //@ close Deque_full_borrow_content(_t, deque)();
        //@ close_full_borrow();
        //@ leak full_borrow(_, _);
        return size;
    }

    pub fn push_front<'a>(deque: &'a mut Deque, value: i32)
    // req Deque(deque, ?elems) &*& length(elems) < 0x7fffffff;
    // ens Deque(deque, cons(value, elems));
    {
        unsafe {
            let new_node = std::alloc::alloc(std::alloc::Layout::new::<Node>()) as *mut Node;
            if new_node.is_null() {
                std::alloc::handle_alloc_error(std::alloc::Layout::new::<Node>());
            }
            //@ close_struct(new_node );
            //@ open_full_borrow(a, Deque_full_borrow_content(_t, deque));
            //@ open Deque_full_borrow_content(_t, deque)();
            (*new_node).prev = (*deque).sentinel;
            (*new_node).value = value;
            //@ let sentinel = (*deque).sentinel;
            //@ open Deque_own(_t, sentinel, _);
            //@ let first = (*sentinel).next;
            (*new_node).next = (*(*deque).sentinel).next;
            (*(*new_node).prev).next = new_node;
            //@ open Nodes(first, sentinel, ?last, sentinel, ?elems);
            (*(*new_node).next).prev = new_node;
            if (*deque).size < 0x7fffffff {
                (*deque).size += 1;
            } else {
                std::process::abort();
            }
            //@ close Deque_own(_t, sentinel, _);
            //@ close Deque_full_borrow_content(_t, deque)();
            //@ close_full_borrow();
            //@ leak full_borrow(_, _);
        }
    }

    pub fn push_back<'a>(deque: &'a mut Deque, value: i32)
    // req Deque(deque, ?elems) &*& length(elems) < 0x7fffffff;
    // ens Deque(deque, append(elems, [value]));
    {
        unsafe {
            let new_node = std::alloc::alloc(std::alloc::Layout::new::<Node>()) as *mut Node;
            if new_node.is_null() {
                std::alloc::handle_alloc_error(std::alloc::Layout::new::<Node>());
            }
            //@ close_struct(new_node );
            //@ open_full_borrow(a, Deque_full_borrow_content(_t, deque));
            //@ open Deque_full_borrow_content(_t, deque)();
            //@ let sentinel = (*deque).sentinel;
            //@ open Deque_own(_t, sentinel, _);
            //@ assert Nodes(_, sentinel, _, sentinel, ?elems);
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
            if (*deque).size < 0x7fffffff {
                (*deque).size += 1;
            } else {
                std::process::abort();
            }
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
            //@ close Deque_own(_t, sentinel, (*deque).size);
            //@ close Deque_full_borrow_content(_t, deque)();
            //@ close_full_borrow();
            //@ leak full_borrow(_, _);
        }
    }

    pub fn pop_front<'a>(deque: &'a mut Deque) -> i32
// req Deque(deque, cons(?elem, ?elems));
    // ens Deque(deque, elems) &*& result == elem;
    {
        unsafe {
            //@ open_full_borrow(a, Deque_full_borrow_content(_t, deque));
            //@ open Deque_full_borrow_content(_t, deque)();
            if (*deque).size == 0 {
                std::process::abort();
            }
            let sentinel = (*deque).sentinel;
            //@ open Deque_own(_t, (*deque).sentinel, _);
            let node = (*sentinel).next;
            //@ open Nodes(_, _, _, _, _);
            let result = (*node).value;
            (*(*node).prev).next = (*node).next;
            //@ open Nodes(_, _, _, _, _);
            (*(*node).next).prev = (*node).prev;
            //@ close Nodes((*node).next, sentinel, _, sentinel, _);
            //@ open_struct(node);
            std::alloc::dealloc(node as *mut u8, std::alloc::Layout::new::<Node>());
            //@ assert (*deque).size > 0;
            // assert (*deque).size < 0x80000000;
            (*deque).size -= 1;
            //@ close Deque_own(_t, sentinel, (*deque).size);
            //@ close Deque_full_borrow_content(_t, deque)();
            //@ close_full_borrow();
            //@ leak full_borrow(_, _);
            return result;
        }
    }

    pub fn pop_back<'a>(deque: &'a mut Deque) -> i32
// req Deque(deque, ?elems) &*& 1 <= length(elems);
        // ens Deque(deque, take(length(elems) - 1, elems)) &*& result == nth(length(elems) - 1, elems);
    {
        unsafe {
            //@ open_full_borrow(a, Deque_full_borrow_content(_t, deque));
            //@ open Deque_full_borrow_content(_t, deque)();
            if (*deque).size == 0 {
                std::process::abort();
            }
            //@ let sentinel = (*deque ).sentinel;
            //@ open Deque_own(_t, sentinel, _);
            //@ let first = (*sentinel).next;
            //@ open Nodes(first, sentinel, _, sentinel, ?elems);
            //@ close Nodes(first, sentinel, _, sentinel, elems);
            let node = (*(*deque).sentinel).prev;
            //@ Nodes_split_last(first);
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
            //@ close Deque_own(_t, sentinel, (*deque).size);
            //@ close Deque_full_borrow_content(_t, deque)();
            //@ close_full_borrow();
            //@ leak full_borrow(_, _);
            return result;
        }
    }

    unsafe fn dispose_nodes(first: *mut Node, lnext: *mut Node)
    //@ req Nodes(first, ?fprev, ?last, lnext, ?elems) &*& Node_next(lnext, _);
    //@ ens Node_next(lnext, _);
    {
        //@ open Nodes(_, _, _, _, _);
        if first == lnext {
            return;
        }
        let next = (*first).next;
        //@ open_struct(first);
        std::alloc::dealloc(first as *mut u8, std::alloc::Layout::new::<Node>());
        Self::dispose_nodes(next, lnext);
    }
    

    fn dispose(deque: Deque)
    // req Deque(deque, []);
    // ens true;
    {
        unsafe {
        //@ open Deque_own(_t, ?sentinel, ?size);
        Self::dispose_nodes((*(deque.sentinel)).next, deque.sentinel);
        //@ open_struct(deque.sentinel);
        std::alloc::dealloc(deque.sentinel as *mut u8, std::alloc::Layout::new::<Node>());
        }
    }
}