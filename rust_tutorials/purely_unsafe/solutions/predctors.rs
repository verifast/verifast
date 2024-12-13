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
        struct_Node_padding(node) &*&
        alloc_block(node as *u8, Layout::new_::<Node<T>>()) &*&
        Nodes(next, ?values0) &*&
        values == cons(value, values0)
    };

pred Stack<T>(stack: *mut Stack<T>, values: list<T>) =
    (*stack).head |-> ?head &*&
    struct_Stack_padding(stack) &*&
    alloc_block(stack as *u8, Layout::new_::<Stack<T>>()) &*&
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
        //@ close_struct(stack);
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
        //@ close_struct(n);
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
        //@ open_struct(head);
        dealloc(head as *mut u8, Layout::new::<Node<T>>());
        //@ close Stack(stack, tail(values));
        result
    }

    unsafe fn dispose(stack: *mut Stack<T>)
    //@ req Stack(stack, nil);
    //@ ens true;
    {
        //@ open Stack(stack, nil);
        //@ open Nodes(_, _);
        //@ open_struct(stack);
        dealloc(stack as *mut u8, Layout::new::<Stack<T>>());
    }

}

unsafe fn input_i32() -> i32
//@ req true;
//@ ens true;
{
    42 // TODO: Actually input a number
}

unsafe fn output_i32(value: i32)
//@ req true;
//@ ens true;
{}

struct Vector {
    x: i32,
    y: i32,
}

/*@

pred_ctor Vector(limit: i32)(v: *mut Vector) =
    (*v).x |-> ?x &*& (*v).y |-> ?y &*&
    struct_Vector_padding(v) &*&
    alloc_block(v as *u8, Layout::new_::<Vector>()) &*&
    x * x + y * y <= limit * limit;

@*/

impl Vector {

    unsafe fn create(limit: i32, x: i32, y: i32) -> *mut Vector
    //@ req true;
    //@ ens Vector(limit)(result);
    {
        if x * x + y * y > limit * limit {
            std::process::abort();
        }
        let result = alloc(Layout::new::<Vector>()) as *mut Vector;
        if result.is_null() {
            handle_alloc_error(Layout::new::<Vector>());
        }
        //@ close_struct(result);
        (*result).x = x;
        (*result).y = y;
        //@ close Vector(limit)(result);
        result
    }
    
}

fn main() {
    unsafe {
        let limit = input_i32();
        let s = Stack::create();
        //@ close foreach(nil, Vector(limit));
        loop {
            //@ inv Stack(s, ?values) &*& foreach(values, Vector(limit));
            let cmd = input_i32();
            match cmd {
                1 => {
                    let x = input_i32();
                    let y = input_i32();
                    let v = Vector::create(limit, x, y);
                    Stack::push(s, v);
                    //@ close foreach(cons(v, values), Vector(limit));
                }
                2 => {
                    if Stack::is_empty(s) {
                        std::process::abort();
                    }
                    let v1 = Stack::pop(s);
                    //@ open foreach(values, Vector(limit));
                    //@ open Vector(limit)(v1);
                    if Stack::is_empty(s) {
                        std::process::abort();
                    }
                    let v2 = Stack::pop(s);
                    //@ open foreach(tail(values), Vector(limit));
                    //@ open Vector(limit)(v2);
                    let sum = Vector::create(limit, (*v1).x + (*v2).x, (*v1).y + (*v2).y);
                    //@ open_struct(v1);
                    dealloc(v1 as *mut u8, Layout::new::<Vector>());
                    //@ open_struct(v2);
                    dealloc(v2 as *mut u8, Layout::new::<Vector>());
                    Stack::push(s, sum);
                    //@ close foreach(cons(sum, tail(tail(values))), Vector(limit));
                }
                3 => {
                    if Stack::is_empty(s) {
                        std::process::abort();
                    }
                    let v_ = Stack::pop(s);
                    //@ open foreach(values, Vector(limit));
                    //@ open Vector(limit)(v_);
                    output_i32((*v_).x);
                    output_i32((*v_).y);
                    //@ open_struct(v_);
                    dealloc(v_ as *mut u8, Layout::new::<Vector>());
                }
                _ => {
                    std::process::abort();
                }
            }
        }
    }
}