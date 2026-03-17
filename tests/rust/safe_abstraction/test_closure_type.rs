// Test for closure type support
// Previously failed with "Closure types are not yet supported"

#![no_std]
#![allow(dead_code)]

fn call_with_one<F: FnOnce(i32) -> i32>(f: F) -> i32
//@ req true;
//@ ens true;
{
    //@ assume(false);
    f(1)
}

fn main()
//@ req true;
//@ ens true;
{
    //@ assume(false);
    let x = 10;
    let result = call_with_one(|a| a + x);
}
