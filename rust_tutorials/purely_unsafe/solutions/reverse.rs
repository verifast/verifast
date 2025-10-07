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

fix i32s_append(values1: i32s, values2: i32s) -> i32s {
    match values1 {
        i32s_nil => values2,
        i32s_cons(h, t) => i32s_cons(h, i32s_append(t, values2)),
    }
}

lem i32s_append_nil_lemma(values: i32s)
    req true;
    ens i32s_append(values, i32s_nil) == values;
{
    match values {
        i32s_nil => {}
        i32s_cons(h, t) => {
            i32s_append_nil_lemma(t);
        }
    }
}

lem i32s_append_assoc_lemma(values1: i32s, values2: i32s, values3: i32s)
    req true;
    ens i32s_append(i32s_append(values1, values2), values3) == i32s_append(values1, i32s_append(values2, values3));
{
    match values1 {
        i32s_nil => {}
        i32s_cons(h, t) => {
            i32s_append_assoc_lemma(t, values2, values3);
        }
    }
}

fix i32s_reverse(values: i32s) -> i32s {
    match values {
        i32s_nil => i32s_nil,
        i32s_cons(h, t) => i32s_append(i32s_reverse(t), i32s_cons(h, i32s_nil))
    }
}

pred Nodes(node: *mut Node, values: i32s) =
    if node == 0 {
        values == i32s_nil
    } else {
        (*node).next |-> ?next &*& (*node).value |-> ?value &*&
        alloc_block_Node(node) &*& Nodes(next, ?values0) &*&
        values == i32s_cons(value, values0)
    };

pred Stack(stack: *mut Stack, values: i32s) =
    (*stack).head |-> ?head &*& alloc_block_Stack(stack) &*& Nodes(head, values);

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
        (*stack).head = std::ptr::null_mut();
        //@ close Nodes(0, i32s_nil);
        //@ close Stack(stack, i32s_nil);
        stack
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
        dealloc(head as *mut u8, Layout::new::<Node>());
        //@ close Stack(stack, i32s_tail(values));
        result
    }
    
    unsafe fn reverse(stack: *mut Stack)
    //@ req Stack(stack, ?values);
    //@ ens Stack(stack, i32s_reverse(values));
    {
        //@ open Stack(stack, values);
        let mut n = (*stack).head;
        let mut m = std::ptr::null_mut();
        //@ close Nodes(m, i32s_nil);
        //@ i32s_append_nil_lemma(i32s_reverse(values));
        loop {
            //@ inv Nodes(m, ?values1) &*& Nodes(n, ?values2) &*& i32s_reverse(values) == i32s_append(i32s_reverse(values2), values1);
            if n.is_null() {
                break;
            }
            //@ open Nodes(n, values2);
            let next = (*n).next;
            //@ assert Nodes(next, ?values2_tail) &*& (*n).value |-> ?value;
            (*n).next = m;
            m = n;
            n = next;
            //@ close Nodes(m, i32s_cons(value, values1));
            //@ i32s_append_assoc_lemma(i32s_reverse(values2_tail), i32s_cons(value, i32s_nil), values1);
        }
        //@ open Nodes(n, _);
        (*stack).head = m;
        //@ close Stack(stack, i32s_reverse(values));
    }

    unsafe fn dispose(stack: *mut Stack)
    //@ req Stack(stack, i32s_nil);
    //@ ens true;
    {
        //@ open Stack(stack, i32s_nil);
        //@ open Nodes(_, _);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }

}

fn main()
//@ req true;
//@ ens true;
{
    unsafe {
        let s = Stack::create();
        Stack::push(s, 10);
        Stack::push(s, 20);
        let result1 = Stack::pop(s);
        //@ assert result1 == 20;
        let result2 = Stack::pop(s);
        //@ assert result2 == 10;
        Stack::dispose(s);
    }
}