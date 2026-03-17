// Test for const generic bool support (Fix 1)
// This should verify successfully after adding bool to the const generic match.

#![no_std]
#![allow(dead_code)]
#![feature(decl_macro)]

fn process<const DELETED: bool>(x: i32) -> i32
//@ req true;
//@ ens result == x;
{
    x
}

fn main()
//@ req true;
//@ ens true;
{
    let a = process::<false>(42);
    let b = process::<true>(10);
    //@ assert a == 42;
    //@ assert b == 10;
}
