// verifast_options{ignore_unwind_paths disable_overflow_check}

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

inductive i32s = i32s_nil | i32s_cons(i32, i32s);

fix i32s_head(values: i32s) -> i32 {
    match values {
        i32s_nil => 0,
        i32s_cons(value, values0) => value,
    }
}

fix i32s_tail(values: i32s) -> i32s {
    match values {
        i32s_nil => i32s_nil,
        i32s_cons(value, values0) => values0,
    }
}

pred Nodes(node: *mut Node, values: i32s) =
    if node == 0 {
        values == i32s_nil
    } else {
        (*node).next |-> ?next &*&
        (*node).value |-> ?value &*&
        struct_Node_padding(node) &*&
        alloc_block(node as *u8, Layout::new_::<Node>()) &*&
        Nodes(next, ?values0) &*&
        values == i32s_cons(value, values0)
    };

pred Stack(stack: *mut Stack, values: i32s) =
    (*stack).head |-> ?head &*&
    struct_Stack_padding(stack) &*&
    alloc_block(stack as *u8, Layout::new_::<Stack>()) &*&
    Nodes(head, values);

fix i32s_sum(values: i32s) -> i32 {
    match values {
        i32s_nil => 0,
        i32s_cons(value, values0) => value + i32s_sum(values0),
    }
}

@*/

unsafe fn get_nodes_sum(node: *mut Node) -> i32
//@ req Nodes(node, ?values);
//@ ens Nodes(node, values) &*& result == i32s_sum(values);
{
    //@ open Nodes(node, values);
    let mut result = 0;
    if !node.is_null() {
        let tail_sum = get_nodes_sum((*node).next);
        result = (*node).value + tail_sum;
    }
    //@ close Nodes(node, values);
    return result;
}

impl Stack {

    unsafe fn create() -> *mut Stack
    //@ req true;
    //@ ens Stack(result, i32s_nil);
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        //@ close_struct(stack);
        (*stack).head = std::ptr::null_mut();
        //@ close Nodes(0, i32s_nil);
        //@ close Stack(stack, i32s_nil);
        return stack;
    }
    
    unsafe fn get_sum(stack: *mut Stack) -> i32
    //@ req Stack(stack, ?values);
    //@ ens Stack(stack, values) &*& result == i32s_sum(values);
    {
        //@ open Stack(stack, values);
        let result = get_nodes_sum((*stack).head);
        //@ close Stack(stack, values);
        return result;
    }
    
    unsafe fn push(stack: *mut Stack, value: i32)
    //@ req Stack(stack, ?values);
    //@ ens Stack(stack, i32s_cons(value, values));
    {
        //@ open Stack(stack, values);
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        //@ close_struct(n);
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
        //@ close Nodes(n, i32s_cons(value, values));
        //@ close Stack(stack, i32s_cons(value, values));
    }
    
    unsafe fn pop(stack: *mut Stack) -> i32
    //@ req Stack(stack, ?values) &*& values != i32s_nil;
    //@ ens Stack(stack, i32s_tail(values)) &*& result == i32s_head(values);
    {
        //@ open Stack(stack, values);
        let head = (*stack).head;
        //@ open Nodes(head, values);
        let result = (*head).value;
        (*stack).head = (*head).next;
        //@ open_struct(head);
        dealloc(head as *mut u8, Layout::new::<Node>());
        //@ close Stack(stack, i32s_tail(values));
        return result;
    }

    unsafe fn dispose(stack: *mut Stack)
    //@ req Stack(stack, i32s_nil);
    //@ ens true;
    {
        //@ open Stack(stack, i32s_nil);
        //@ open Nodes(_, _);
        //@ open_struct(stack);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }

}

fn main() {
    unsafe {
        let s = Stack::create();
        Stack::push(s, 10);
        Stack::push(s, 20);
        let sum = Stack::get_sum(s);
        //@ assert sum == 30;
        let result1 = Stack::pop(s);
        //@ assert result1 == 20;
        let result2 = Stack::pop(s);
        //@ assert result2 == 10;
        Stack::dispose(s);
    }
}