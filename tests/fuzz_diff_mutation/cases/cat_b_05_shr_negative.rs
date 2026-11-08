// verifast_options{skip_specless_fns}
#![feature(core_intrinsics)]
#![allow(internal_features)]
use std::intrinsics::unchecked_shr;

pub unsafe fn bad_shr(a: i32, s: u32) -> i32
//@ req true;
//@ ens true;
{
    unchecked_shr(a, s)
}
fn main() {}
