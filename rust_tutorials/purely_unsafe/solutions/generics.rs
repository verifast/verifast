// verifast_options{ignore_unwind_paths}

use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};
//@ use std::alloc::{Layout, alloc_block};

struct Node<T> {
    next: *mut Node<T>,
    value: T,
}

struct Stack<T> {
    head: *mut Node<T>,
}

/*@

pred Nodes<T>(node: *mut Node<T>, values: list<T>) =
    if node == 0 {
        values == nil
    } else {
        (*node).next |-> ?next &*&
        (*node).value |-> ?value &*&
        alloc_block_Node(node) &*&
        Nodes(next, ?values0) &*&
        values == cons(value, values0)
    };

pred Stack<T>(stack: *mut Stack<T>, values: list<T>) =
    (*stack).head |-> ?head &*&
    alloc_block_Stack(stack) &*&
    Nodes(head, values);

@*/

impl<T> Stack<T> {

    unsafe fn create() -> *mut Stack<T>
    //@ req true;
    //@ ens Stack(result, nil);
    {
        let stack = alloc(Layout::new::<Stack<T>>()) as *mut Stack<T>;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack<T>>());
        }
        (*stack).head = std::ptr::null_mut();
        //@ close Nodes::<T>(0, nil);
        //@ close Stack(stack, nil);
        return stack;
    }
    
    unsafe fn push(stack: *mut Stack<T>, value: T)
    //@ req Stack(stack, ?values);
    //@ ens Stack(stack, cons(value, values));
    {
        //@ open Stack(stack, values);
        let n = alloc(Layout::new::<Node<T>>()) as *mut Node<T>;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node<T>>());
        }
        (*n).next = (*stack).head;
        (&raw mut (*n).value).write(value);
        (*stack).head = n;
        //@ close Nodes(n, cons(value, values));
        //@ close Stack(stack, cons(value, values));
    }
    
    unsafe fn is_empty(stack: *mut Stack<T>) -> bool
    //@ req Stack(stack, ?values);
    //@ ens Stack(stack, values) &*& result == (values == nil);
    {
        //@ open Stack(stack, values);
        let head = (*stack).head;
        //@ open Nodes(head, values);
        let result = head.is_null();
        //@ close Nodes(head, values);
        //@ close Stack(stack, values);
        result
    }
    
    unsafe fn pop(stack: *mut Stack<T>) -> T
    //@ req Stack(stack, ?values) &*& values != nil;
    //@ ens Stack(stack, tail(values)) &*& result == head(values);
    {
        //@ open Stack(stack, values);
        let head = (*stack).head;
        //@ open Nodes(head, values);
        (*stack).head = (*head).next;
        let result = (&raw mut (*head).value).read();
        //@ close Node_value(head, _);
        dealloc(head as *mut u8, Layout::new::<Node<T>>());
        //@ close Stack(stack, tail(values));
        result
    }

    unsafe fn reverse(stack: *mut Stack<T>)
    //@ req Stack(stack, ?values);
    //@ ens Stack(stack, reverse(values));
    {
        //@ open Stack(stack, values);
        let mut n = (*stack).head;
        let mut m = std::ptr::null_mut();
        //@ close Nodes(m, nil);
        //@ append_nil(reverse(values));
        loop {
            //@ inv Nodes(m, ?values1) &*& Nodes(n, ?values2) &*& reverse(values) == append(reverse(values2), values1);
            //@ open Nodes(n, values2);
            if n.is_null() {
                break;
            }
            let next = (*n).next;
            //@ assert Nodes(next, ?values2tail) &*& (*n).value |-> ?value;
            (*n).next = m;
            m = n;
            n = next;
            //@ close Nodes(m, cons(value, values1));
            //@ append_assoc(reverse(values2tail), cons(value, nil), values1);
        }
        (*stack).head = m;
        //@ close Stack(stack, reverse(values));
    }

    unsafe fn dispose(stack: *mut Stack<T>)
    //@ req Stack(stack, nil);
    //@ ens true;
    {
        //@ open Stack(stack, nil);
        //@ open Nodes(_, _);
        dealloc(stack as *mut u8, Layout::new::<Stack<T>>());
    }

}

struct Point {
    x: i32,
    y: i32,
}

impl Point {

    unsafe fn create(x: i32, y: i32) -> *mut Point
    //@ req true;
    //@ ens (*result).x |-> x &*& (*result).y |-> y &*& alloc_block_Point(result);
    {
        let result = alloc(Layout::new::<Point>()) as *mut Point;
        if result.is_null() {
            handle_alloc_error(Layout::new::<Point>());
        }
        (*result).x = x;
        (*result).y = y;
        result
    }
    
}

fn main() {
    unsafe {
        let s = Stack::create();
        let p1 = Point::create(10, 0);
        let p2 = Point::create(0, 10);
        Stack::push(s, p1);
        Stack::push(s, p2);
        Stack::reverse(s);
        std::process::abort();
    }
}
