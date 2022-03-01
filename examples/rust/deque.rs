use std::mem::MaybeUninit;
use std::ptr::addr_of_mut;

struct Node {
    prev: *mut Node,
    value: i32,
    next: *mut Node
}

unsafe fn create_deque() -> *mut Node {
    let sentinel: *mut Node = (*Box::into_raw(Box::new(MaybeUninit::<Node>::uninit()))).as_mut_ptr();
    addr_of_mut!((*sentinel).prev).write(sentinel);
    addr_of_mut!((*sentinel).next).write(sentinel);
    return sentinel;
}

unsafe fn push_front(deque: *mut Node, value: i32) {
    let n: *mut Node = (*Box::into_raw(Box::new(MaybeUninit::<Node>::uninit()))).as_mut_ptr();
    addr_of_mut!((*n).prev).write(deque);
    addr_of_mut!((*n).value).write(value);
    addr_of_mut!((*n).next).write((*deque).next);
    (*(*n).prev).next = n;
    (*(*n).next).prev = n;
}

unsafe fn push_back(deque: *mut Node, value: i32) {
    let n: *mut Node = (*Box::into_raw(Box::new(MaybeUninit::<Node>::uninit()))).as_mut_ptr();
    addr_of_mut!((*n).prev).write((*deque).prev);
    addr_of_mut!((*n).value).write(value);
    addr_of_mut!((*n).next).write(deque);
    (*(*n).prev).next = n;
    (*(*n).next).prev = n;
}

unsafe fn is_empty(deque: *mut Node) -> bool {
    return (*deque).next == deque;
}

unsafe fn pop_front(deque: *mut Node) -> i32
// precondition: deque is not empty
{
    let n = (*deque).next;
    let result = (*n).value;
    (*(*n).prev).next = (*n).next;
    (*(*n).next).prev = (*n).prev;
    Box::from_raw(n); // causes it to get dropped.
    return result;
}

unsafe fn pop_back(deque: *mut Node) -> i32
// precondition: deque is not empty
{
    let n = (*deque).prev;
    let result = (*n).value;
    (*(*n).prev).next = (*n).next;
    (*(*n).next).prev = (*n).prev;
    Box::from_raw(n);
    return result;
}

unsafe fn drop_deque(deque: *mut Node)
// precondition: the deque is empty
{
    Box::from_raw(deque);
}

unsafe fn main_() {
    let deque = create_deque();
    assert!(is_empty(deque));
    push_front(deque, 10);
    assert!(!is_empty(deque));
    push_back(deque, 20);
    push_front(deque, 30);
    push_back(deque, 40);
    assert!(pop_front(deque) == 30);
    assert!(pop_back(deque) == 40);
    assert!(pop_front(deque) == 10);
    assert!(pop_back(deque) == 20);
    drop_deque(deque);
}

fn main() {
    unsafe {
        main_();
    }
}
