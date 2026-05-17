// Test for division support in SwitchInt translator
// Previously crashed with "Pattern matching failed" at translate_sw_int

#![no_std]
#![allow(dead_code)]

fn half(x: usize) -> usize {
    x / 2
}

fn div_signed(x: i32, y: i32) -> i32
//@ req y != 0;
//@ ens true;
{
    //@ assume(false);
    x / y
}
