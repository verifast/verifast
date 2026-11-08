// verifast_options{skip_specless_fns}
#![feature(core_intrinsics)]
#![allow(internal_features)]
use std::intrinsics::unchecked_mul;

pub unsafe fn test_unchecked_mul(a: u32, b: u32) -> u32
//@ req a == 25 &*& b == 40;
//@ ens result == 1000;
{
    unchecked_mul(a, b)
}
fn main() {}
