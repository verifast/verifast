// verifast_options{skip_specless_fns}

// Unchecked arithmetic intrinsics (MIR `AddUnchecked`, `SubUnchecked`, `MulUnchecked`,
// `ShlUnchecked`, `ShrUnchecked`) and the `<<` / `>>` operators.

#![feature(core_intrinsics)]
#![allow(internal_features)]

use std::intrinsics::{unchecked_add, unchecked_mul, unchecked_shl, unchecked_shr, unchecked_sub};

unsafe fn sub(a: usize, b: usize) -> usize
//@ req b <= a;
//@ ens result == a - b;
{
    unchecked_sub(a, b)
}

unsafe fn add(a: u8, b: u8) -> u8
//@ req a + b <= 255;
//@ ens result == a + b;
{
    unchecked_add(a, b)
}

unsafe fn mul(a: u32, b: u32) -> u32
//@ req a <= 1000 &*& b == 7;
//@ ens result == a * 7;
{
    unchecked_mul(a, b)
}

// Bits shifted out are discarded (no overflow check), with a symbolic shift amount.
unsafe fn shl_u32(x: u32, n: u32) -> u32
//@ req n < 32;
//@ ens result <= 4294967295;
{
    unchecked_shl(x, n)
}

unsafe fn shl_u8_wrapping(x: u8) -> u8
//@ req x == 255;
//@ ens true;
{
    x << 4
}

unsafe fn shr_u64(x: u64, n: u32) -> u64
//@ req n < 64;
//@ ens true;
{
    unchecked_shr(x, n)
}

// No integer promotion: `x << 4` on a `u8` is a `u8`.
unsafe fn shl_u8(x: u8) -> u8
//@ req x < 16;
//@ ens result == x * 16;
{
    x << 4
}

// Rust defines `>>` on negative signed integers (arithmetic shift) and `<<` on them.
fn shr_i32(x: i32) -> i32
//@ req true;
//@ ens true;
{
    x >> 1
}

unsafe fn shl_i8(x: i8) -> i8
//@ req x == -1;
//@ ens true;
{
    x << 1
}

// Must fail: the subtraction may overflow.
unsafe fn sub_unconstrained(a: usize, b: usize) -> usize
//@ req true;
//@ ens true;
{
    unchecked_sub(a, b) //~should_fail
} //~allow_dead_code

// Must fail: the bit width of a `u8` is 8, not the 32 of a promoted `int`.
unsafe fn shl_u8_by_8(x: u8, n: u32) -> u8
//@ req n <= 8 &*& x == 0;
//@ ens true;
{
    x << n //~should_fail
} //~allow_dead_code

// Must fail: the shift amount may reach the bit width.
unsafe fn shr_u32_by_32(x: u32, n: u32) -> u32
//@ req n <= 32;
//@ ens true;
{
    unchecked_shr(x, n) //~should_fail
} //~allow_dead_code

fn main() {}
