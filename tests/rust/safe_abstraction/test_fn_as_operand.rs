// Test for functions as operands in rvalues
// Previously failed with "Todo: Functions as operand in rvalues are not supported yet"

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
