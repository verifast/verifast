// verifast_options{skip_specless_fns}
#![feature(core_intrinsics)]
#![allow(internal_features)]
use std::intrinsics::unchecked_sub;

pub unsafe fn bad_sub(a: u32, b: u32) -> u32
//@ req true;
//@ ens true;
{
    unchecked_sub(a, b)
}
fn main() {}
