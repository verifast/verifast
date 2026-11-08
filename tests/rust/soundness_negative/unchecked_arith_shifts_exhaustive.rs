// verifast_options{skip_specless_fns}

#![feature(core_intrinsics)]
#![allow(internal_features)]

use std::intrinsics::{unchecked_add, unchecked_mul, unchecked_shl, unchecked_shr, unchecked_sub};

// =========================================================================
// POSITIVE CASES: Exact shift identities, bounds, and truncation facts
// =========================================================================

// Shift by 0 is identity across unsigned and signed types
unsafe fn test_shl_zero_u8(x: u8) -> u8
//@ req true;
//@ ens result == x;
{
    x << 0
}

unsafe fn test_shl_zero_u16(x: u16) -> u16
//@ req true;
//@ ens result == x;
{
    x << 0
}

unsafe fn test_shl_zero_u32(x: u32) -> u32
//@ req true;
//@ ens result == x;
{
    x << 0
}

unsafe fn test_shl_zero_u64(x: u64) -> u64
//@ req true;
//@ ens result == x;
{
    x << 0
}

unsafe fn test_shl_zero_u128(x: u128) -> u128
//@ req true;
//@ ens result == x;
{
    x << 0
}

unsafe fn test_shl_zero_usize(x: usize) -> usize
//@ req true;
//@ ens result == x;
{
    x << 0
}

unsafe fn test_shl_zero_i8(x: i8) -> i8
//@ req true;
//@ ens result == x;
{
    x << 0
}

unsafe fn test_shl_zero_i16(x: i16) -> i16
//@ req true;
//@ ens result == x;
{
    x << 0
}

unsafe fn test_shl_zero_i32(x: i32) -> i32
//@ req true;
//@ ens result == x;
{
    x << 0
}

unsafe fn test_shl_zero_i64(x: i64) -> i64
//@ req true;
//@ ens result == x;
{
    x << 0
}

// In-range left shifts equal x * 2^k
unsafe fn test_shl_in_range_u8(x: u8) -> u8
//@ req x < 64;
//@ ens result == x * 4;
{
    x << 2
}

unsafe fn test_shl_in_range_u16(x: u16) -> u16
//@ req x < 8192;
//@ ens result == x * 8;
{
    x << 3
}

unsafe fn test_shl_in_range_u32(x: u32) -> u32
//@ req x < 268435456;
//@ ens result == x * 16;
{
    x << 4
}

unsafe fn test_shl_in_range_u64(x: u64) -> u64
//@ req x < 576460752303423488;
//@ ens result == x * 32;
{
    x << 5
}

unsafe fn test_shl_in_range_i16(x: i16) -> i16
//@ req -4096 <= x &*& x <= 4095;
//@ ens result == x * 4;
{
    x << 2
}

unsafe fn test_shl_in_range_i32(x: i32) -> i32
//@ req -268435456 <= x &*& x <= 268435455;
//@ ens result == x * 8;
{
    x << 3
}

// Bit-discarding left shifts stay within type bounds
unsafe fn test_shl_discard_u16(x: u16) -> u16
//@ req x == 0xffff;
//@ ens 0 <= result &*& result <= 65535;
{
    x << 4
}

unsafe fn test_shl_discard_u32(x: u32) -> u32
//@ req x == 0x80000001;
//@ ens 0 <= result &*& result <= 4294967295;
{
    x << 1
}

unsafe fn test_shl_discard_u64(x: u64) -> u64
//@ req x == 0x8000000000000001;
//@ ens 0 <= result &*& result <= 18446744073709551615;
{
    x << 1
}

unsafe fn test_shl_discard_i16(x: i16) -> i16
//@ req x == 20000;
//@ ens -32768 <= result &*& result <= 32767;
{
    x << 2
}

unsafe fn test_shl_discard_i32(x: i32) -> i32
//@ req x == 2000000000;
//@ ens -2147483648 <= result &*& result <= 2147483647;
{
    x << 1
}

unsafe fn test_shl_discard_i64(x: i64) -> i64
//@ req x == 5000000000000000000;
//@ ens -9223372036854775808 <= result &*& result <= 9223372036854775807;
{
    x << 2
}

// Right shifts on signed integers satisfy bounds
unsafe fn test_shr_i8_range(x: i8, k: u32) -> i8
//@ req k < 8;
//@ ens -128 <= result &*& result <= 127;
{
    x >> k
}

unsafe fn test_shr_i16_range(x: i16, k: u32) -> i16
//@ req k < 16;
//@ ens -32768 <= result &*& result <= 32767;
{
    x >> k
}

unsafe fn test_shr_i32_range(x: i32, k: u32) -> i32
//@ req k < 32;
//@ ens -2147483648 <= result &*& result <= 2147483647;
{
    x >> k
}

unsafe fn test_shr_i64_range(x: i64, k: u32) -> i64
//@ req k < 64;
//@ ens -9223372036854775808 <= result &*& result <= 9223372036854775807;
{
    x >> k
}

// Valid unchecked arithmetic
unsafe fn test_valid_add_u128(a: u128, b: u128) -> u128
//@ req a <= 1000 &*& b <= 2000;
//@ ens result == a + b;
{
    unchecked_add(a, b)
}

unsafe fn test_valid_sub_usize(a: usize, b: usize) -> usize
//@ req b <= a;
//@ ens result == a - b;
{
    unchecked_sub(a, b)
}

unsafe fn test_valid_mul_i64(a: i64, b: i64) -> i64
//@ req -100 <= a &*& a <= 100 &*& b == 7;
//@ ens result == a * 7;
{
    unchecked_mul(a, b)
}

// =========================================================================
// NEGATIVE CASES: 19 should_fail cases
// =========================================================================

// 1. unchecked_add overflow on u8::MAX + 1
unsafe fn neg_add_u8_overflow(a: u8, b: u8) -> u8
//@ req a == 255 &*& b == 1;
//@ ens true;
{
    unchecked_add(a, b) //~should_fail
} //~allow_dead_code

// 2. unchecked_add overflow on i32::MAX + 1
unsafe fn neg_add_i32_overflow(a: i32, b: i32) -> i32
//@ req a == 2147483647 &*& b == 1;
//@ ens true;
{
    unchecked_add(a, b) //~should_fail
} //~allow_dead_code

// 3. unchecked_add overflow on u128::MAX + 1
unsafe fn neg_add_u128_overflow(a: u128, b: u128) -> u128
//@ req a == 340282366920938463463374607431768211455 &*& b == 1;
//@ ens true;
{
    unchecked_add(a, b) //~should_fail
} //~allow_dead_code

// 4. unchecked_add signed underflow on i8::MIN + -1
unsafe fn neg_add_i8_underflow(a: i8, b: i8) -> i8
//@ req a == -128 &*& b == -1;
//@ ens true;
{
    unchecked_add(a, b) //~should_fail
} //~allow_dead_code

// 5. unchecked_sub underflow on 0u32 - 1
unsafe fn neg_sub_u32_underflow(a: u32, b: u32) -> u32
//@ req a == 0 &*& b == 1;
//@ ens true;
{
    unchecked_sub(a, b) //~should_fail
} //~allow_dead_code

// 6. unchecked_sub underflow on i8::MIN - 1
unsafe fn neg_sub_i8_underflow(a: i8, b: i8) -> i8
//@ req a == -128 &*& b == 1;
//@ ens true;
{
    unchecked_sub(a, b) //~should_fail
} //~allow_dead_code

// 7. unchecked_sub unsigned underflow on 0usize - 1
unsafe fn neg_sub_usize_underflow(a: usize, b: usize) -> usize
//@ req a == 0 &*& b == 1;
//@ ens true;
{
    unchecked_sub(a, b) //~should_fail
} //~allow_dead_code

// 8. unchecked_mul overflow on 100u8 * 3
unsafe fn neg_mul_u8_overflow(a: u8, b: u8) -> u8
//@ req a == 100 &*& b == 3;
//@ ens true;
{
    unchecked_mul(a, b) //~should_fail
} //~allow_dead_code

// 9. unchecked_mul overflow on i16::MIN * -1
unsafe fn neg_mul_i16_overflow(a: i16, b: i16) -> i16
//@ req a == -32768 &*& b == -1;
//@ ens true;
{
    unchecked_mul(a, b) //~should_fail
} //~allow_dead_code

// 10. unchecked_mul overflow on i64::MAX * 2
unsafe fn neg_mul_i64_overflow(a: i64, b: i64) -> i64
//@ req a == 9223372036854775807 &*& b == 2;
//@ ens true;
{
    unchecked_mul(a, b) //~should_fail
} //~allow_dead_code

// 11. unchecked_shl with shift amount >= 8 on u8
unsafe fn neg_shl_u8_by_8(x: u8, n: u32) -> u8
//@ req n >= 8;
//@ ens true;
{
    unchecked_shl(x, n) //~should_fail
} //~allow_dead_code

// 12. << with shift amount >= 16 on u16
unsafe fn neg_shl_u16_by_16(x: u16, n: u32) -> u16
//@ req n >= 16;
//@ ens true;
{
    x << n //~should_fail
} //~allow_dead_code

// 13. << with shift amount >= 32 on u32
unsafe fn neg_shl_u32_by_32(x: u32, n: u32) -> u32
//@ req n >= 32;
//@ ens true;
{
    x << n //~should_fail
} //~allow_dead_code

// 14. << with shift amount >= 64 on u64
unsafe fn neg_shl_u64_by_64(x: u64, n: u32) -> u64
//@ req n >= 64;
//@ ens true;
{
    x << n //~should_fail
} //~allow_dead_code

// 15. << with shift amount >= 128 on u128
unsafe fn neg_shl_u128_by_128(x: u128, n: u32) -> u128
//@ req n >= 128;
//@ ens true;
{
    x << n //~should_fail
} //~allow_dead_code

// 16. unchecked_shr with shift amount >= 32 on i32
unsafe fn neg_shr_i32_by_32(x: i32, n: u32) -> i32
//@ req n >= 32;
//@ ens true;
{
    unchecked_shr(x, n) //~should_fail
} //~allow_dead_code

// 17. >> with shift amount < 0 (negative shift amount)
unsafe fn neg_shr_by_negative(x: i32, n: i32) -> i32
//@ req n < 0;
//@ ens true;
{
    x >> n //~should_fail
} //~allow_dead_code

// 18. False postcondition: claiming discarded bits are preserved on u16
unsafe fn neg_shl_u16_false_post(x: u16) -> u16
//@ req x == 0x8001;
//@ ens result == 65538; //~should_fail
{
    x << 1
}

// 19. False postcondition: claiming u8 overflow into sign bit is positive
unsafe fn neg_shl_i8_false_post(x: i8) -> i8
//@ req x == 64;
//@ ens result == 128; //~should_fail
{
    x << 1
}

fn main() {}
