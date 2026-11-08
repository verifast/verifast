// verifast_options{skip_specless_fns}
#![feature(core_intrinsics)]
#![allow(internal_features)]
use std::intrinsics::unchecked_mul;

pub unsafe fn bad_mul(a: u8, b: u8) -> u8
//@ req true;
//@ ens true;
{
    unchecked_mul(a, b)
}
fn main() {}
