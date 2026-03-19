// Test for preliminary closure type support
// Previously failed with "Closure types are not yet supported"
//
// LIMITATIONS:
// - Closures are translated as opaque struct types (captures are not modeled)
// - Closure bodies are NOT verified (require assume(false) guards)

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
