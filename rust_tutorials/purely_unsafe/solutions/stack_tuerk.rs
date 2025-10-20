// verifast_options{disable_overflow_check}
//@ use std::alloc::{Layout, alloc_block};

struct Node {
    next: *mut Node,
    value: i32,
}

/*@

pred Nodes(node: *mut Node, count: i32) =
    if node == 0 {
        count == 0
    } else {
        0 < count &*&
        (*node).next |-> ?next &*& (*node).value |-> ?value &*&
        alloc_block_Node(node) &*& Nodes(next, count - 1)
    };

@*/

struct Stack {
    head: *mut Node,
}

/*@

pred Stack(stack: *mut Stack, count: i32) =
    (*stack).head |-> ?head &*& alloc_block_Stack(stack) &*& Nodes(head, count);

@*/

unsafe fn stack_get_count(stack: *mut Stack) -> i32
//@ req Stack(stack, ?count);
//@ ens Stack(stack, count) &*& result == count;
{
    //@ open Stack(stack, count);
    let mut n = (*stack).head;
    let mut i = 0;
    loop {
        /*@
        req Nodes(n, ?count1);
        ens Nodes(old_n, count1) &*& i == old_i + count1;
        @*/
        //@ open Nodes(n, count1);
        //@ if n == 0 { close Nodes(n, count1); }
        if n.is_null() {
            break;
        }
        n = (*n).next;
        i += 1;
        //@ recursive_call();
        //@ close Nodes(old_n, count1);
    }
    //@ close Stack(stack, count);
    i
}
