// verifast_options{skip_specless_fns}
#![feature(core_intrinsics)]
#![allow(internal_features)]
use std::intrinsics::unchecked_shl;

pub unsafe fn bad_shl(a: u32, s: u32) -> u32
//@ req true;
//@ ens true;
{
    unchecked_shl(a, s)
}
fn main() {}
