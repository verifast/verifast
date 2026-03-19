// Test for functions as operands in rvalues (Fix 2)
// This should verify successfully after handling TrTypedConstantFn.

#![no_std]
#![allow(dead_code)]

fn identity(x: i32) -> i32 { x }

fn apply(f: fn(i32) -> i32, x: i32) -> i32
//@ req true;
//@ ens true;
{
    //@ assume(false);
    f(x)
}

fn main()
//@ req true;
//@ ens true;
{
    //@ assume(false);
    let result = apply(identity, 42);
}
