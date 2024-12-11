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

fn_type I32Func(data_pred: pred(*mut u8)) = unsafe fn(data: *mut u8, x: i32) -> i32;
    req data_pred(data);
    ens data_pred(data);

@*/

type I32Func = unsafe fn(*mut u8, i32) -> i32;

unsafe fn map_nodes(n: *mut Node, f: I32Func, data: *mut u8)
//@ req Nodes(n, ?count) &*& [_]is_I32Func(f, ?data_pred) &*& data_pred(data);
//@ ens Nodes(n, count) &*& data_pred(data);
{
    //@ open Nodes(n, _);
    if !n.is_null() {
        let y = f(data, (*n).value);
        (*n).value = y;
        map_nodes((*n).next, f, data);
    }
    //@ close Nodes(n, count);
}

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
    
    unsafe fn map(stack: *mut Stack, f: I32Func, data: *mut u8)
    //@ req Stack(stack, ?count) &*& [_]is_I32Func(f, ?data_pred) &*& data_pred(data);
    //@ ens Stack(stack, count) &*& data_pred(data);
    {
        //@ open Stack(stack, _);
        map_nodes((*stack).head, f, data);
        //@ close Stack(stack, count);
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

//@ pred plus_a_data(data: *mut u8) = *(data as *i32) |-> ?_;

unsafe fn plus_a(data: *mut u8, x: i32) -> i32
//@ req plus_a_data(data);
//@ ens plus_a_data(data);
{
    //@ open plus_a_data(data);
    let result = x + *(data as *mut i32);
    //@ close plus_a_data(data);
    result
}

fn main() {
    unsafe {
        let s = Stack::create();
        Stack::push(s, 10);
        Stack::push(s, 20);
        Stack::push(s, 30);
        let mut a = 42;
        //@ close plus_a_data(&a as *u8);
        /*@
        produce_fn_ptr_chunk I32Func(plus_a)(plus_a_data)(data, x) {
            call();
        }
        @*/
        Stack::map(s, plus_a, &raw mut a as *mut u8);
        //@ open plus_a_data(_);
        Stack::dispose(s);
    }
}
