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
        struct_Node_padding(node) &*&
        alloc_block(node as *u8, Layout::new_::<Node>()) &*&
        Nodes(next, count - 1)
    };

pred Stack(stack: *mut Stack, count: i32) =
    (*stack).head |-> ?head &*&
    struct_Stack_padding(stack) &*&
    alloc_block(stack as *u8, Layout::new_::<Stack>()) &*&
    0 <= count &*&
    Nodes(head, count);

@*/

unsafe fn dispose_nodes(n: *mut Node)
//@ req Nodes(n, _);
//@ ens true;
{
    //@ open Nodes(n, _);
    if !n.is_null() {
        dispose_nodes((*n).next);
        //@ open_struct(n);
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
        //@ close_struct(stack);
        (*stack).head = std::ptr::null_mut();
        //@ close Nodes(0, 0);
        //@ close Stack(stack, 0);
        return stack;
    }
    
    unsafe fn is_empty(stack: *mut Stack) -> bool
    //@ req Stack(stack, ?count);
    //@ ens Stack(stack, count) &*& result == (count == 0);
    {
        //@ open Stack(stack, count);
        let head = (*stack).head;
        //@ open Nodes(head, count);
        let result = (*stack).head.is_null();
        //@ close Nodes(head, count);
        //@ close Stack(stack, count);
        return result;
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
        //@ close_struct(n);
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
        //@ open_struct(head);
        dealloc(head as *mut u8, Layout::new::<Node>());
        //@ close Stack(stack, count - 1);
        return result;
    }
    
    unsafe fn dispose(stack: *mut Stack)
    //@ req Stack(stack, _);
    //@ ens true;
    {
        //@ open Stack(stack, _);
        dispose_nodes((*stack).head);
        //@ open_struct(stack);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }

}

fn main() {
    unsafe {
        let s = Stack::create();
        Stack::push(s, 10);
        Stack::push(s, 20);
        Stack::pop(s);
        Stack::pop(s);
        Stack::dispose(s);
    }
}
