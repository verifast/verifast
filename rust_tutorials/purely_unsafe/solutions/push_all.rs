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

pred lseg(first: *mut Node, last: *mut Node, count: i32) =
    if first == last {
        count == 0
    } else {
        0 < count &*& first != 0 &*&
        (*first).value |-> ?value &*& (*first).next |-> ?next &*&
        struct_Node_padding(first) &*&
        alloc_block(first as *mut u8, Layout::new_::<Node>()) &*&
        lseg(next, last, count - 1)
    };

lem Nodes_to_lseg_lemma(first: *mut Node)
    req Nodes(first, ?count);
    ens lseg(first, 0, count);
{
    open Nodes(first, count);
    if first != 0 {
        Nodes_to_lseg_lemma((*first).next);
    }
    close lseg(first, 0, count);
}

lem lseg_to_Nodes_lemma(first: *mut Node)
    req lseg(first, 0, ?count);
    ens Nodes(first, count);
{
    open lseg(first, 0, count);
    if first != 0 {
        lseg_to_Nodes_lemma((*first).next);
    }
    close Nodes(first, count);
}

lem lseg_add_lemma(first: *mut Node)
    req lseg(first, ?last, ?count) &*& last != 0 &*& (*last).value |-> ?last_value &*& (*last).next |-> ?next &*&
        struct_Node_padding(last) &*& alloc_block(last as *u8, Layout::new_::<Node>()) &*&
        lseg(next, 0, ?count0);
    ens lseg(first, next, count + 1) &*& lseg(next, 0, count0);
{
    open lseg(first, last, count);
    if first == last {
        close lseg(next, next, 0);
    } else {
        lseg_add_lemma((*first).next);
    }
    open lseg(next, 0, count0);
    close lseg(next, 0, count0);
    close lseg(first, next, count + 1);
}

lem lseg_append_lemma(first: *mut Node)
    req lseg(first, ?n, ?count) &*& lseg(n, 0, ?count0);
    ens lseg(first, 0, count + count0);
{
    open lseg(first, n, count);
    if first != n {
        open lseg(n, 0, count0);
        close lseg(n, 0, count0);
        lseg_append_lemma((*first).next);
        close lseg(first, 0, count + count0);
    }
}

@*/

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

    unsafe fn get_count(stack: *mut Stack) -> i32
    //@ req Stack(stack, ?count);
    //@ ens Stack(stack, count) &*& result == count;
    {
        //@ open Stack(stack, count);
        let head = (*stack).head;
        //@ Nodes_to_lseg_lemma(head);
        let mut n = head;
        let mut i = 0;
        //@ close lseg(head, head, 0);
        loop {
            //@ inv lseg(head, n, i) &*& lseg(n, 0, count - i);
            if n.is_null() {
                break;
            }
            //@ open lseg(n, 0, count - i);
            n = (*n).next;
            i += 1;
            //@ lseg_add_lemma(head);
        }
        //@ open lseg(0, 0, _);
        //@ lseg_to_Nodes_lemma(head);
        //@ close Stack(stack, count);
        return i;
    }

    unsafe fn push_all(stack: *mut Stack, other: *mut Stack)
    //@ req Stack(stack, ?count) &*& Stack(other, ?count0);
    //@ ens Stack(stack, count0 + count);
    {
        //@ open Stack(stack, count);
        //@ Nodes_to_lseg_lemma((*stack).head);
        //@ open Stack(other, count0);
        //@ Nodes_to_lseg_lemma((*other).head);
        let head0 = (*other).head;
        //@ open_struct(other);
        dealloc(other as *mut u8, Layout::new::<Stack>());
        let mut n = head0;
        //@ open lseg(head0, 0, count0);
        if !n.is_null() {
            //@ close lseg(head0, head0, 0);
            loop {
                /*@
                inv lseg(head0, n, ?count1) &*& n != 0 &*& (*n).value |-> ?n_value &*& 
                    (*n).next |-> ?next &*& struct_Node_padding(n) &*&
                    alloc_block(n as *u8, Layout::new_::<Node>()) &*&
                    lseg(next, 0, count0 - count1 - 1);
                @*/
                if (*n).next.is_null() {
                    break;
                }
                n = (*n).next;
                //@ lseg_add_lemma(head0);
                //@ open lseg(next, 0, count0 - count1 - 1);
            }
            //@ open lseg(0, 0, _);
            (*n).next = (*stack).head;
            //@ lseg_add_lemma(head0);
            //@ lseg_append_lemma(head0);
            (*stack).head = head0;
        }
        //@ lseg_to_Nodes_lemma((*stack).head);
        //@ close Stack(stack, count0 + count);
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
    //@ req Stack(stack, 0);
    //@ ens true;
    {
        //@ open Stack(stack, 0);
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
        Stack::pop(s);
        Stack::pop(s);
        Stack::dispose(s);
    }
}
