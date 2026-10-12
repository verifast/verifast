// Contracts of functions declared inside function bodies, and ghost commands in their bodies.

unsafe fn outer(x: u8) -> u8
//@ req x < 100;
//@ ens result == x + 1;
{
    unsafe fn incr(y: u8) -> u8
    //@ req y < 255;
    //@ ens result == y + 1;
    {
        y + 1
    }

    let r = incr(x);
    //@ assert r == x + 1;
    r
}

fn outer_without_spec() {
    unsafe fn double(y: u8) -> u8
    /*@ req y < 128; @*/
    /*@ ens result == 2 * y; @*/
    {
        y * 2
    }

    unsafe { double(21); }
}

// A method of a type declared in a function body.
unsafe fn nested_impl(p: *mut u8)
//@ req *p |-> _;
//@ ens *p |-> 42;
{
    struct Writer;

    impl Writer {
        unsafe fn write(p: *mut u8, v: u8)
        //@ req *p |-> _;
        //@ ens *p |-> v;
        {
            *p = v;
        }
    }

    Writer::write(p, 42);
}

// A Drop impl, with a contract, of a type declared in a function body.
unsafe fn nested_drop_impl()
//@ req thread_token(?t) &*& t == currentThread;
//@ ens thread_token(t);
{
    struct Guard { pub y: u8 }

    impl Drop for Guard {
        fn drop(&mut self)
        //@ req thread_token(?t) &*& *self |-> ?v;
        //@ ens thread_token(t) &*& *self |-> v;
        /*@
        safety_proof {
            open <nested_drop_impl::Guard>.full_borrow_content(_t, self)();
            open nested_drop_impl::Guard_own(_t, _);
            call();
            open_points_to(self);
        }
        @*/
        {
        }
    }

    let g = Guard { y: 1 };
    //@ close nested_drop_impl::Guard_own(t, g);
}

fn nested_ghost_command() {
    fn id(z: u8) -> u8 {
        let w = z;
        //@ assert w == z;
        w
    }
    id(5);
}

fn nested_wrong_ghost_command() {
    fn id(z: u8) -> u8 {
        //@ assert z == 5; //~should_fail
        z
    }
    id(5);
}

unsafe fn nested_wrong_contract()
//@ req true;
//@ ens true;
{
    unsafe fn incr(y: u8) -> u8
    //@ req y < 255;
    //@ ens result == y; //~should_fail
    {
        y + 1
    }
    incr(1);
}

macro_rules! ignore { ($($t:tt)*) => {} }

fn consume(_x: u8) {}

// A ghost command after `fn` inside a word or inside a macro invocation is not part of a nested function's contract.
fn fn_inside_word(b: bool) {
    let x1fn: u8 = 0;
    if b { consume(x1fn) }
    //@ assert false; //~should_fail
}

fn fn_inside_macro_invocation() {
    ignore! { fn foo }
    //@ assert false; //~should_fail
}

fn main() {}
