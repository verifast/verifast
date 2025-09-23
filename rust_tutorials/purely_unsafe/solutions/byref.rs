// verifast_options{ignore_unwind_paths}

use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};
//@ use std::alloc::{Layout, alloc_block};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

/*@

pred Nodes(node: *mut Node, count: i32) =
    if node == 0 {
        count == 0
    } else {
        0 < count &*&
        (*node).next |-> ?next &*&
        (*node).value |-> ?value &*&
        alloc_block_Node(node) &*&
        Nodes(next, count - 1)
    };

pred Stack(stack: *mut Stack, count: i32) =
    (*stack).head |-> ?head &*&
    alloc_block_Stack(stack) &*&
    0 <= count &*&
    Nodes(head, count);

fn_type I32Predicate() = unsafe fn(x: i32) -> bool;
    req true;
    ens true;

@*/

type I32Predicate = unsafe fn(i32) -> bool;

unsafe fn filter_nodes(n: *mut *mut Node, p: I32Predicate)
//@ req *n |-> ?node &*& Nodes(node, _) &*& [_]is_I32Predicate(p);
//@ ens *n |-> ?node0 &*& Nodes(node0, _);
{
    if !(*n).is_null() {
        //@ open Nodes(node, _);
        let keep = p((**n).value);
        if keep {
            //@ open Node_next(node, _);
            filter_nodes(&raw mut (**n).next, p);
            //@ close Node_next(node, ?next);
            //@ open Nodes(next, ?count);
            //@ close Nodes(next, count);
            //@ close Nodes(node, count + 1);
        } else {
            let next_ = (**n).next;
            dealloc(*n as *mut u8, Layout::new::<Node>());
            *n = next_;
            filter_nodes(n, p);
        }
    }
}

unsafe fn dispose_nodes(n: *mut Node)
//@ req Nodes(n, _);
//@ ens true;
{
    //@ open Nodes(n, _);
    if !n.is_null() {
        dispose_nodes((*n).next);
        dealloc(n as *mut u8, Layout::new::<Node>());
    }
}

impl Stack {

    unsafe fn create() -> *mut Stack
    //@ req true;
    //@ ens Stack(result, 0);
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        //@ close Nodes(0, 0);
        //@ close Stack(stack, 0);
        return stack;
    }
    
    unsafe fn push(stack: *mut Stack, value: i32)
    //@ req Stack(stack, ?count);
    //@ ens Stack(stack, count + 1);
    {
        //@ open Stack(stack, count);
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
        //@ close Nodes(n, count + 1);
        //@ close Stack(stack, count + 1);
    }

    unsafe fn pop(stack: *mut Stack) -> i32
    //@ req Stack(stack, ?count) &*& 0 < count;
    //@ ens Stack(stack, count - 1);
    {
        //@ open Stack(stack, count);
        let head = (*stack).head;
        //@ open Nodes(head, count);
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        //@ close Stack(stack, count - 1);
        return result;
    }
    
    unsafe fn filter(stack: *mut Stack, p: I32Predicate)
    //@ req Stack(stack, _) &*& [_]is_I32Predicate(p);
    //@ ens Stack(stack, _);
    {
        //@ open Stack(stack, _);
        //@ open Stack_head(stack, _);
        filter_nodes(&raw mut (*stack).head, p);
        //@ close Stack_head(stack, ?head);
        //@ open Nodes(head, ?count);
        //@ close Nodes(head, count);
        //@ close Stack(stack, count);
    }
    
    unsafe fn dispose(stack: *mut Stack)
    //@ req Stack(stack, _);
    //@ ens true;
    {
        //@ open Stack(stack, _);
        dispose_nodes((*stack).head);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }

}

unsafe fn neq_20(x: i32) -> bool
//@ req true;
//@ ens true;
{
    x != 20
}

fn main() {
    unsafe {
        let s = Stack::create();
        Stack::push(s, 10);
        Stack::push(s, 20);
        /*@
        produce_fn_ptr_chunk I32Predicate(neq_20)()(x) {
            call();
        }
        @*/
        Stack::filter(s, neq_20);
        Stack::dispose(s);
    }
}
