// Division by a non-constant divisor: rustc emits an `Assert` terminator for the
// zero check (and the overflow check for signed division) before the `Div`.
// Previously the translator crashed on the `Assert` terminator ("Pattern matching failed").
//
// These are safe functions, so they must accept every input; on a zero divisor the
// `Assert` panics (an abort under -ignore_unwind_paths) and the `Div` is only reached,
// and only has to be proven safe, on the path where the check passed.

#![no_std]
#![allow(dead_code)]

fn half(x: usize) -> usize {
    x / 2
}

fn div_unsigned(x: usize, y: usize) -> usize
//@ req true;
//@ ens result == x / y;
//@ on_unwind_ens false;
{
    x / y
}

// Signed division is not covered here: its overflow check (`x == i32::MIN && y == -1`) is
// lowered to a `BitAnd` of two booleans, which the translator does not support yet.
