// verifast_options{skip_specless_fns}
#![feature(core_intrinsics)]
#![allow(internal_features)]
use std::intrinsics::unchecked_add;

pub unsafe fn bad_add(a: u8, b: u8) -> u8
//@ req true;
//@ ens true;
{
    unchecked_add(a, b)
}
fn main() {}
