unsafe fn assert(b: bool)
//@ requires b;
//@ ensures true;
{}

struct Node {
    prev: *mut Node,
    value: i32,
    next: *mut Node,
}

/*@

predicate Nodes(struct Node *n, struct Node *prev, struct Node *last, struct Node *next; list<int> elems) =
    n == next ?
        elems == {} &*& last == prev
    :
        malloc_block(n, sizeof(struct Node)) &*& struct_Node_padding(n) &*&
        n->prev |-> prev &*&
        n->value |-> ?value &*&
        n->next |-> ?next0 &*&
        Nodes(next0, n, last, next, ?elems0) &*&
        elems == cons(value, elems0);

lemma void Nodes_split_last(struct Node *n)
    requires Nodes(n, ?prev, ?last, ?next, ?elems) &*& 1 <= length(elems);
    ensures
        Nodes(n, prev, ?last1, last, take(length(elems) - 1, elems)) &*&
        malloc_block(last, sizeof(struct Node)) &*& struct_Node_padding(last) &*&
        last->prev |-> last1 &*&
        last->value |-> nth(length(elems) - 1, elems) &*&
        last->next |-> next;
{
    open Nodes(n, prev, last, next, elems);
    struct Node *next0 = n->next;
    if (length(elems) == 1) {
        open Nodes(_, _, _, _, _);
        close Nodes(n, prev, prev, n, {});
    } else {
        Nodes_split_last(n->next);
        assert Nodes(next0, n, ?last1, last, _);
        close Nodes(n, prev, last1, last, _);
    }
}

lemma void Nodes_join_last(struct Node *n)
    requires
        Nodes(n, ?prev, ?last1, ?last, ?elems1) &*&
        malloc_block(last, sizeof(struct Node)) &*& struct_Node_padding(last) &*&
        last->prev |-> last1 &*&
        last->value |-> ?value &*&
        last->next |-> ?next &*& next->next |-> ?nextNext;
    ensures
        Nodes(n, prev, last, next, append(elems1, {value})) &*& next->next |-> nextNext;
{
    open Nodes(n, prev, last1, last, elems1);
    struct Node *next0 = n->next;
    if (1 <= length(elems1)) {
        Nodes_join_last(next0);
    }
}

@*/

struct Deque {
    sentinel: *mut Node,
    size: i32
}

/*@

predicate Deque(struct Deque *deque; list<int> elems) =
    malloc_block(deque, sizeof(struct Deque)) &*& struct_Deque_padding(deque) &*&
    deque->sentinel |-> ?sentinel &*&
    malloc_block(sentinel, sizeof(struct Node)) &*& struct_Node_padding(sentinel) &*&
    sentinel->prev |-> ?last &*&
    sentinel->value |-> _ &*&
    sentinel->next |-> ?first &*&
    Nodes(first, sentinel, last, sentinel, elems) &*&
    deque->size |-> length(elems);

@*/

unsafe fn create_deque() -> *mut Deque
//@ requires true;
//@ ensures Deque(result, {});
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

unsafe fn deque_get_size(deque: *mut Deque) -> i32
//@ requires Deque(deque, ?elems);
//@ ensures Deque(deque, elems) &*& result == length(elems);
{
    return (*deque).size;
}

unsafe fn deque_push_front(deque: *mut Deque, value: i32)
//@ requires Deque(deque, ?elems) &*& length(elems) < 0x7fffffff;
//@ ensures Deque(deque, cons(value, elems));
{
    let new_node = std::alloc::alloc(std::alloc::Layout::new::<Node>()) as *mut Node;
    if new_node.is_null() {
        std::alloc::handle_alloc_error(std::alloc::Layout::new::<Node>());
    }
    //@ close_struct(new_node);
    (*new_node).prev = (*deque).sentinel;
    (*new_node).value = value;
    //@ struct Node *sentinel = deque->sentinel;
    //@ struct Node *first = sentinel->next;
    (*new_node).next = (*(*deque).sentinel).next;
    (*(*new_node).prev).next = new_node;
    //@ open Nodes(first, sentinel, ?last, sentinel, elems);
    (*(*new_node).next).prev = new_node;
    (*deque).size += 1;
}

unsafe fn deque_push_back(deque: *mut Deque, value: i32)
//@ requires Deque(deque, ?elems) &*& length(elems) < 0x7fffffff;
//@ ensures Deque(deque, append(elems, {value}));
{
    let new_node = std::alloc::alloc(std::alloc::Layout::new::<Node>()) as *mut Node;
    if new_node.is_null() {
        std::alloc::handle_alloc_error(std::alloc::Layout::new::<Node>());
    }
    //@ close_struct(new_node);
    //@ struct Node *sentinel = deque->sentinel;
    (*new_node).prev = (*(*deque).sentinel).prev;
    (*new_node).value = value;
    (*new_node).next = (*deque).sentinel;
    /*@
    if (length(elems) > 0)
        Nodes_split_last(sentinel->next);
    else
        open Nodes(?first, sentinel, ?last, sentinel, elems);
    @*/
    (*(*new_node).prev).next = new_node;
    (*(*new_node).next).prev = new_node;
    (*deque).size += 1;
    /*@
    if (length(elems) > 0) {
        Nodes_join_last(sentinel->next);
        append_take_drop_n(elems, length(elems) - 1);
        drop_n_plus_one(length(elems) - 1, elems);
    } else
        close Nodes(new_node, sentinel, sentinel, new_node, {});
    @*/
    //@ Nodes_join_last(sentinel->next);
}

unsafe fn deque_pop_front(deque: *mut Deque) -> i32
//@ requires Deque(deque, cons(?elem, ?elems));
//@ ensures Deque(deque, elems) &*& result == elem;
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

unsafe fn deque_pop_back(deque: *mut Deque) -> i32
//@ requires Deque(deque, ?elems) &*& 1 <= length(elems);
//@ ensures Deque(deque, take(length(elems) - 1, elems)) &*& result == nth(length(elems) - 1, elems);
{
    //@ struct Node *sentinel = deque->sentinel;
    //@ struct Node *first = sentinel->next;
    //@ Nodes_split_last(first);
    let node = (*(*deque).sentinel).prev;
    let result = (*node).value;
    /*@
    if (2 <= length(elems)) {
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
    if (2 <= length(elems))
        Nodes_join_last(first);
    @*/
    return result;
}

unsafe fn deque_dispose(deque: *mut Deque)
//@ requires Deque(deque, {});
//@ ensures true;
{
    //@ open_struct(deque->sentinel);
    std::alloc::dealloc((*deque).sentinel as *mut u8, std::alloc::Layout::new::<Node>());
    //@ open_struct(deque);
    std::alloc::dealloc(deque as *mut u8, std::alloc::Layout::new::<Deque>());
    //@ open Nodes(_, _, _, _, _);
}

fn main() {
    unsafe {
        let deque = create_deque();
        deque_push_back(deque, 10);
        deque_push_front(deque, -10);
        deque_push_back(deque, 20);
        deque_push_front(deque, -20);
        assert(deque_get_size(deque) == 4);
        assert(deque_pop_back(deque) == 20);
        assert(deque_pop_back(deque) == 10);
        assert(deque_pop_front(deque) == -20);
        assert(deque_pop_front(deque) == -10);
        deque_dispose(deque);
    }
}
