unsafe fn assert(b: bool)
//@ req b;
//@ ens true;
{
}

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

struct Deque {
    sentinel: *mut Node,
    size: i32,
}

/*@

pred Deque(deque: *Deque; elems: list<i32>) =
    alloc_block(deque, std::mem::size_of::<Deque>()) &*& struct_Deque_padding(deque) &*&
    (*deque).sentinel |-> ?sentinel &*&
    alloc_block(sentinel, std::mem::size_of::<Node>()) &*& struct_Node_padding(sentinel) &*&
    (*sentinel).prev |-> ?last &*&
    (*sentinel).value |-> _ &*&
    (*sentinel).next |-> ?first &*&
    Nodes(first, sentinel, last, sentinel, elems) &*&
    (*deque).size |-> length(elems);

@*/

impl Deque {
    unsafe fn new() -> *mut Deque
//@ req true;
    //@ ens Deque(result, []);
    {
        let deque = std::alloc::alloc(std::alloc::Layout::new::<Deque>()) as *mut Deque;
        if deque.is_null() {
            std::alloc::handle_alloc_error(std::alloc::Layout::new::<Deque>());
        }
        //@ close_struct(deque);
        let sentinel = std::alloc::alloc(std::alloc::Layout::new::<Node>()) as *mut Node;
        if sentinel.is_null() {
            std::alloc::handle_alloc_error(std::alloc::Layout::new::<Node>());
        }
        //@ close_struct(sentinel);
        (*sentinel).prev = sentinel;
        (*sentinel).next = sentinel;
        (*deque).size = 0;
        (*deque).sentinel = sentinel;
        return deque;
    }

    unsafe fn get_size(deque: *mut Deque) -> i32
//@ req Deque(deque, ?elems);
    //@ ens Deque(deque, elems) &*& result == length(elems);
    {
        return (*deque).size;
    }

    unsafe fn push_front(deque: *mut Deque, value: i32)
    //@ req Deque(deque, ?elems) &*& length(elems) < 0x7fffffff;
    //@ ens Deque(deque, cons(value, elems));
    {
        let new_node = std::alloc::alloc(std::alloc::Layout::new::<Node>()) as *mut Node;
        if new_node.is_null() {
            std::alloc::handle_alloc_error(std::alloc::Layout::new::<Node>());
        }
        //@ close_struct(new_node );
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

    unsafe fn push_back(deque: *mut Deque, value: i32)
    //@ req Deque(deque, ?elems) &*& length(elems) < 0x7fffffff;
    //@ ens Deque(deque, append(elems, [value]));
    {
        let new_node = std::alloc::alloc(std::alloc::Layout::new::<Node>()) as *mut Node;
        if new_node.is_null() {
            std::alloc::handle_alloc_error(std::alloc::Layout::new::<Node>());
        }
        //@ close_struct(new_node );
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

    unsafe fn pop_front(deque: *mut Deque) -> i32
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

    unsafe fn pop_back(deque: *mut Deque) -> i32
//@ req Deque(deque, ?elems) &*& 1 <= length(elems);
    //@ ens Deque(deque, take(length(elems) - 1, elems)) &*& result == nth(length(elems) - 1, elems);
    {
        //@ let sentinel = (*deque ) . sentinel;
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

    unsafe fn dispose(deque: *mut Deque)
    //@ req Deque(deque, []);
    //@ ens true;
    {
        //@ open_struct((*deque ) . sentinel);
        std::alloc::dealloc(
            (*deque).sentinel as *mut u8,
            std::alloc::Layout::new::<Node>(),
        );
        //@ open_struct(deque);
        std::alloc::dealloc(deque as *mut u8, std::alloc::Layout::new::<Deque>());
        //@ open Nodes(_, _, _, _, _);
    }

    unsafe fn swap(d: *mut Deque, d1: *mut Deque)
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
        let deque = Deque::new();
        Deque::push_back(deque, 10);
        Deque::push_front(deque, -10);
        Deque::push_back(deque, 20);
        Deque::push_front(deque, -20);
        assert(Deque::get_size(deque) == 4);
        assert(Deque::pop_back(deque) == 20);
        assert(Deque::pop_back(deque) == 10);
        assert(Deque::pop_front(deque) == -20);
        assert(Deque::pop_front(deque) == -10);
        Deque::dispose(deque);
    }
}
