// Test for const generic bool support
// Previously failed with "Unsupported constant type or size"

#![no_std]
#![allow(dead_code)]

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
