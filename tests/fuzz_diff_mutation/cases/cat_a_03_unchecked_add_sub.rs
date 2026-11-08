// verifast_options{skip_specless_fns}
#![feature(core_intrinsics)]
#![allow(internal_features)]
use std::intrinsics::{unchecked_add, unchecked_sub};

pub unsafe fn test_unchecked_add_sub(a: u8, b: u8, c: u8) -> u8
//@ req a == 100 &*& b == 50 &*& c == 30;
//@ ens result == 120;
{
    let sum = unchecked_add(a, b);
    unchecked_sub(sum, c)
}
fn main() {}
