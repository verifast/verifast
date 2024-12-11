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

@*/

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
