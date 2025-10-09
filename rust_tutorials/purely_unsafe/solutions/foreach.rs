// verifast_options{ignore_unwind_paths disable_overflow_check}
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
        (*node).next |-> ?next &*& (*node).value |-> ?value &*&
        alloc_block_Node(node) &*& Nodes(next, ?values0) &*&
        values == cons(value, values0)
    };

pred Stack<T>(stack: *mut Stack<T>, values: list<T>) =
    (*stack).head |-> ?head &*& alloc_block_Stack(stack) &*& Nodes(head, values);

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
        stack
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

    unsafe fn dispose(stack: *mut Stack<T>)
    //@ req Stack(stack, nil);
    //@ ens true;
    {
        //@ open Stack(stack, nil);
        //@ open Nodes(_, _);
        dealloc(stack as *mut u8, Layout::new::<Stack<T>>());
    }

}

unsafe fn input_char() -> char
//@ req true;
//@ ens true;
//@ assume_correct
{
    let mut line = String::new();
    std::io::stdin().read_line(&mut line).unwrap();
    line.chars().next().unwrap()
}

unsafe fn input_i32() -> i32
//@ req true;
//@ ens true;
//@ assume_correct
{
    let mut line = String::new();
    std::io::stdin().read_line(&mut line).unwrap();
    line.trim().parse().unwrap()
}

unsafe fn output_i32(value: i32)
//@ req true;
//@ ens true;
//@ assume_correct
{
    println!("{}", value);
}

struct Vector {
    x: i32,
    y: i32,
}

/*@

pred Vector(v: *mut Vector) =
    (*v).x |-> ?x &*& (*v).y |-> ?y &*&
    alloc_block_Vector(v);

@*/

impl Vector {

    unsafe fn create(x: i32, y: i32) -> *mut Vector
    //@ req true;
    //@ ens Vector(result);
    {
        let result = alloc(Layout::new::<Vector>()) as *mut Vector;
        if result.is_null() {
            handle_alloc_error(Layout::new::<Vector>());
        }
        (*result).x = x;
        (*result).y = y;
        //@ close Vector(result);
        result
    }
    
}

fn main() {
    unsafe {
        let s = Stack::create();
        //@ close foreach(nil, Vector);
        loop {
            //@ inv Stack(s, ?values) &*& foreach(values, Vector);
            let cmd = input_char();
            match cmd {
                'p' => {
                    let x = input_i32();
                    let y = input_i32();
                    let v = Vector::create(x, y);
                    Stack::push(s, v);
                    //@ close foreach(cons(v, values), Vector);
                }
                '+' => {
                    assert!(!Stack::is_empty(s), "Stack underflow");
                    let v1 = Stack::pop(s);
                    //@ open foreach(values, Vector);
                    //@ open Vector(v1);
                    assert!(!Stack::is_empty(s), "Stack underflow");
                    let v2 = Stack::pop(s);
                    //@ open foreach(tail(values), Vector);
                    //@ open Vector(v2);
                    let sum = Vector::create((*v1).x + (*v2).x, (*v1).y + (*v2).y);
                    dealloc(v1 as *mut u8, Layout::new::<Vector>());
                    dealloc(v2 as *mut u8, Layout::new::<Vector>());
                    Stack::push(s, sum);
                    //@ close foreach(cons(sum, tail(tail(values))), Vector);
                }
                '=' => {
                    assert!(!Stack::is_empty(s), "Stack underflow");
                    let v_ = Stack::pop(s);
                    //@ open foreach(values, Vector);
                    //@ open Vector(v_);
                    output_i32((*v_).x);
                    output_i32((*v_).y);
                    dealloc(v_ as *mut u8, Layout::new::<Vector>());
                }
                _ => {
                    std::process::abort();
                }
            }
        }
    }
}
