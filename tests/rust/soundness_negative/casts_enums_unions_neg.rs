// verifast_options{skip_specless_fns}

#![feature(core_intrinsics)]
#![allow(internal_features)]

use std::cmp::Ordering;
//@ use std::cmp::Ordering;
use std::intrinsics::{unchecked_div, unchecked_rem};

pub enum TrafficLight {
    Red,
    Yellow,
    Green,
}

// =========================================================================
// POSITIVE CASES: In-range casts, valid division, and correct enum matching
// =========================================================================

// Widening casts preserve value exactly
pub fn test_valid_widen_u8_to_u32(x: u8) -> u32
//@ req true;
//@ ens result == x;
{
    x as u32
}

pub fn test_valid_widen_i16_to_i32(x: i16) -> i32
//@ req true;
//@ ens result == x;
{
    x as i32
}

// In-range narrowing cast proves value preservation
pub unsafe fn test_valid_narrow_u32_to_u8(x: u32) -> u8
//@ req x <= 255;
//@ ens result == x;
{
    x as u8
}

// In-range signed narrowing cast
pub unsafe fn test_valid_narrow_i32_to_i16(x: i32) -> i16
//@ req -32768 <= x &*& x <= 32767;
//@ ens result == x;
{
    x as i16
}

// In-range unsigned to signed cast
pub unsafe fn test_valid_u16_to_i32(x: u16) -> i32
//@ req true;
//@ ens result == x;
{
    x as i32
}

// Valid unchecked division and remainder
pub unsafe fn test_valid_udiv(x: u32, y: u32) -> u32
//@ req y == 5;
//@ ens result == x / 5;
{
    unchecked_div(x, y)
}

pub unsafe fn test_valid_urem(x: u32, y: u32) -> u32
//@ req y == 4;
//@ ens result == x % 4;
{
    unchecked_rem(x, y)
}

// Verified enum match reversing ordering
pub unsafe fn test_valid_reverse_ordering(o: Ordering) -> Ordering
//@ req true;
/*@
ens result == match o {
        Ordering::Less => Ordering::Greater,
        Ordering::Equal => Ordering::Equal,
        Ordering::Greater => Ordering::Less,
    };
@*/
{
    match o {
        Ordering::Less => Ordering::Greater,
        Ordering::Equal => Ordering::Equal,
        Ordering::Greater => Ordering::Less,
    }
}

// Verified custom enum match
pub unsafe fn test_valid_next_light(light: TrafficLight) -> TrafficLight
//@ req true;
/*@
ens result == match light {
        TrafficLight::Red => TrafficLight::Green,
        TrafficLight::Yellow => TrafficLight::Red,
        TrafficLight::Green => TrafficLight::Yellow, //~allow_dead_code
    };
@*/
{
    match light {
        TrafficLight::Red => TrafficLight::Green,
        TrafficLight::Yellow => TrafficLight::Red,
        TrafficLight::Green => TrafficLight::Yellow, //~allow_dead_code
    }
}

// =========================================================================
// NEGATIVE CASES: 10 should_fail cases
// =========================================================================

// 1. Narrowing cast u32 to u8 when value exceeds u8::MAX (potential overflow)
pub unsafe fn neg_narrow_u32_to_u8(x: u32) -> u8
//@ req x == 300;
//@ ens true;
{
    x as u8 //~should_fail
} //~allow_dead_code

// 2. Narrowing cast u16 to u8 on 256
pub unsafe fn neg_narrow_u16_to_u8(x: u16) -> u8
//@ req x == 256;
//@ ens true;
{
    x as u8 //~should_fail
} //~allow_dead_code

// 3. Narrowing cast i32 to i16 when value exceeds i16::MAX
pub unsafe fn neg_narrow_i32_to_i16(x: i32) -> i16
//@ req x == 40000;
//@ ens true;
{
    x as i16 //~should_fail
} //~allow_dead_code

// 4. Signed to unsigned cast on negative value
pub unsafe fn neg_signed_to_unsigned(x: i32) -> u32
//@ req x == -1;
//@ ens true;
{
    x as u32 //~should_fail
} //~allow_dead_code

// 5. Unsigned to signed cast when value exceeds i32::MAX
pub unsafe fn neg_unsigned_to_signed(x: u32) -> i32
//@ req x == 3000000000;
//@ ens true;
{
    x as i32 //~should_fail
} //~allow_dead_code

// 6. Unchecked division by zero
pub unsafe fn neg_unchecked_div_by_zero(x: u32, y: u32) -> u32
//@ req y == 0;
//@ ens true;
{
    unchecked_div(x, y) //~should_fail
} //~allow_dead_code

// 7. Unchecked remainder by zero
pub unsafe fn neg_unchecked_rem_by_zero(x: u32, y: u32) -> u32
//@ req y == 0;
//@ ens true;
{
    unchecked_rem(x, y) //~should_fail
} //~allow_dead_code

// 8. Signed division overflow on i32::MIN / -1
pub unsafe fn neg_unchecked_sdiv_overflow(x: i32, y: i32) -> i32
//@ req x == -2147483648 &*& y == -1;
//@ ens true;
{
    unchecked_div(x, y) //~should_fail
} //~allow_dead_code

// 9. Enum discriminant match with wrong postcondition on Ordering::Greater
pub unsafe fn neg_enum_match_wrong_arm(o: Ordering) -> Ordering
//@ req true;
/*@
ens result == match o { //~should_fail
        Ordering::Less => Ordering::Greater,
        Ordering::Equal => Ordering::Equal,
        Ordering::Greater => Ordering::Equal,
    };
@*/
{
    match o {
        Ordering::Less => Ordering::Greater,
        Ordering::Equal => Ordering::Equal,
        Ordering::Greater => Ordering::Less,
    }
}

// 10. Custom enum discriminant match with wrong postcondition on Yellow arm
pub unsafe fn neg_custom_enum_wrong_arm(light: TrafficLight) -> TrafficLight
//@ req true;
/*@
ens result == match light { //~should_fail
        TrafficLight::Red => TrafficLight::Green,
        TrafficLight::Yellow => TrafficLight::Green,
        TrafficLight::Green => TrafficLight::Yellow, //~allow_dead_code
    };
@*/
{
    match light {
        TrafficLight::Red => TrafficLight::Green,
        TrafficLight::Yellow => TrafficLight::Red,
        TrafficLight::Green => TrafficLight::Yellow, //~allow_dead_code
    }
}

fn main() {}
