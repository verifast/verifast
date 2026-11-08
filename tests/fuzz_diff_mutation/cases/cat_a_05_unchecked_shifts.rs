// verifast_options{skip_specless_fns}
#![feature(core_intrinsics)]
#![allow(internal_features)]
use std::intrinsics::{unchecked_shl, unchecked_shr};

pub unsafe fn test_unchecked_shifts(x: u32, s1: u32, s2: u32) -> u32
//@ req x == 4 &*& s1 == 3 &*& s2 == 2;
//@ ens 0 <= result &*& result <= 4294967295;
{
    let l = unchecked_shl(x, s1);
    unchecked_shr(l, s2)
}
fn main() {}
