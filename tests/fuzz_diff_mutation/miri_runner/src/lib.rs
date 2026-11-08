#![feature(core_intrinsics)]
#![allow(internal_features)]
#![allow(unused_assignments)]
#![allow(dead_code)]

use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};
use std::intrinsics::{unchecked_add, unchecked_mul, unchecked_shl, unchecked_shr, unchecked_sub};

// ==========================================
// Category A: Safe / Verified Unsafe
// ==========================================

pub unsafe fn cat_a_01_raw_ptr_fn() -> i32 {
    let mut x: i32 = 0;
    let p = &raw mut x;
    unsafe {
        *p = 42;
        *p
    }
}

pub struct RawSlice {
    pub v: *mut [i32],
    pub n: usize,
}

pub unsafe fn cat_a_02_raw_slice_fn(s: *mut RawSlice, w: *mut [i32]) -> *mut [i32] {
    unsafe {
        let old = (*s).v;
        (*s).v = w;
        old
    }
}

pub unsafe fn cat_a_03_unchecked_add_sub_fn(a: u8, b: u8, c: u8) -> u8 {
    unsafe {
        let sum = unchecked_add(a, b);
        unchecked_sub(sum, c)
    }
}

pub unsafe fn cat_a_04_unchecked_mul_fn(a: u32, b: u32) -> u32 {
    unsafe { unchecked_mul(a, b) }
}

pub unsafe fn cat_a_05_unchecked_shifts_fn(x: u32, s1: u32, s2: u32) -> u32 {
    unsafe {
        let l = unchecked_shl(x, s1);
        unchecked_shr(l, s2)
    }
}

pub unsafe fn cat_a_06_bit_shifts_fn() -> (u8, i32) {
    let u: u8 = 255;
    let discarded: u8 = u << 4;
    let neg: i32 = -16;
    let arith: i32 = neg >> 2;
    (discarded, arith)
}

pub struct Point {
    pub x: i32,
    pub y: i32,
}

pub unsafe fn cat_a_07_struct_field_fn() -> i32 {
    let mut pt = Point { x: 10, y: 20 };
    let p = &raw mut pt;
    unsafe {
        (*p).x = 99;
        (*p).x
    }
}

pub unsafe fn cat_a_08_tuple_proj_fn(p: *mut (i32, i32)) -> i32 {
    unsafe { (*p).0 + (*p).1 }
}

pub unsafe fn cat_a_09_alloc_dealloc_fn() -> u8 {
    unsafe {
        let layout = Layout::new::<u8>();
        let p = alloc(layout);
        if p.is_null() {
            handle_alloc_error(layout);
        }
        *p = 42;
        let v = *p;
        dealloc(p, layout);
        v
    }
}

pub unsafe fn cat_a_10_ptr_swap_fn(a: *mut i32, b: *mut i32) {
    unsafe {
        let tmp = *a;
        *a = *b;
        *b = tmp;
    }
}

// ==========================================
// Category B: Undefined Behavior Functions
// ==========================================

pub unsafe fn cat_b_01_add_overflow_fn() -> u8 {
    unsafe { unchecked_add(255u8, 1u8) }
}

pub unsafe fn cat_b_02_sub_underflow_fn() -> u32 {
    unsafe { unchecked_sub(0u32, 1u32) }
}

pub unsafe fn cat_b_03_mul_overflow_fn() -> u8 {
    unsafe { unchecked_mul(200u8, 2u8) }
}

pub unsafe fn cat_b_04_shl_bitwidth_fn() -> u32 {
    unsafe { unchecked_shl(1u32, 32u32) }
}

pub unsafe fn cat_b_05_shr_negative_fn() -> i32 {
    unsafe { unchecked_shr(1i32, 32u32) }
}

pub unsafe fn cat_b_06_null_deref_fn() -> i32 {
    unsafe {
        let p = std::ptr::null::<i32>();
        *p
    }
}

pub unsafe fn cat_b_07_use_after_free_fn() -> u8 {
    unsafe {
        let layout = Layout::new::<u8>();
        let p = alloc(layout);
        if p.is_null() {
            handle_alloc_error(layout);
        }
        *p = 77;
        dealloc(p, layout);
        *p
    }
}

pub unsafe fn cat_b_08_double_free_fn() {
    unsafe {
        let layout = Layout::new::<u8>();
        let p = alloc(layout);
        if p.is_null() {
            handle_alloc_error(layout);
        }
        *p = 77;
        dealloc(p, layout);
        dealloc(p, layout);
    }
}

pub unsafe fn cat_b_09_uninit_read_fn() -> u8 {
    unsafe {
        let layout = Layout::new::<u8>();
        let p = alloc(layout);
        if p.is_null() {
            handle_alloc_error(layout);
        }
        let v = *p;
        dealloc(p, layout);
        v
    }
}

pub unsafe fn cat_b_10_out_of_bounds_fn() -> i32 {
    unsafe {
        let mut x: i32 = 42;
        let p = &raw mut x;
        *p.add(4)
    }
}

// ==========================================
// Category C: Known Open Issues
// ==========================================

pub unsafe fn cat_c_01_issue_947_fn() -> i32 {
    unsafe {
        let p: *mut i32;
        {
            let mut x: i32 = 42;
            p = &raw mut x;
            *p = 100;
        }
        *p
    }
}

pub unsafe fn cat_c_02_issue_685_fn() -> i32 {
    unsafe {
        let mut x: i32 = 10;
        let raw_ptr = &raw mut x;
        let ref_mut = &mut *raw_ptr;
        *ref_mut = 20;
        let val = *raw_ptr;
        *ref_mut = 30;
        val
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_cat_a_01_raw_ptr() {
        assert_eq!(unsafe { cat_a_01_raw_ptr_fn() }, 42);
    }

    #[test]
    fn test_cat_a_02_raw_slice() {
        let mut arr1 = [1, 2, 3];
        let mut arr2 = [4, 5, 6, 7];
        let mut s = RawSlice { v: &raw mut arr1 as *mut [i32], n: 3 };
        let old = unsafe { cat_a_02_raw_slice_fn(&raw mut s, &raw mut arr2 as *mut [i32]) };
        assert_eq!(old as *mut i32, &raw mut arr1 as *mut i32);
        assert_eq!(s.v as *mut i32, &raw mut arr2 as *mut i32);
    }

    #[test]
    fn test_cat_a_03_unchecked_add_sub() {
        assert_eq!(unsafe { cat_a_03_unchecked_add_sub_fn(100, 50, 30) }, 120);
    }

    #[test]
    fn test_cat_a_04_unchecked_mul() {
        assert_eq!(unsafe { cat_a_04_unchecked_mul_fn(25, 40) }, 1000);
    }

    #[test]
    fn test_cat_a_05_unchecked_shifts() {
        assert_eq!(unsafe { cat_a_05_unchecked_shifts_fn(4, 3, 2) }, 8);
    }

    #[test]
    fn test_cat_a_06_bit_shifts() {
        let (discarded, arith) = unsafe { cat_a_06_bit_shifts_fn() };
        assert_eq!(discarded, 240);
        assert_eq!(arith, -4);
    }

    #[test]
    fn test_cat_a_07_struct_field() {
        assert_eq!(unsafe { cat_a_07_struct_field_fn() }, 99);
    }

    #[test]
    fn test_cat_a_08_tuple_proj() {
        let mut pair = (100, 250);
        assert_eq!(unsafe { cat_a_08_tuple_proj_fn(&raw mut pair) }, 350);
    }

    #[test]
    fn test_cat_a_09_alloc_dealloc() {
        assert_eq!(unsafe { cat_a_09_alloc_dealloc_fn() }, 42);
    }

    #[test]
    fn test_cat_a_10_ptr_swap() {
        let mut a = 111;
        let mut b = 222;
        unsafe { cat_a_10_ptr_swap_fn(&raw mut a, &raw mut b); }
        assert_eq!(a, 222);
        assert_eq!(b, 111);
    }

    // UB Tests (expected to fail under Miri)
    #[test]
    fn test_cat_b_01_add_overflow() {
        unsafe { cat_b_01_add_overflow_fn(); }
    }

    #[test]
    fn test_cat_b_02_sub_underflow() {
        unsafe { cat_b_02_sub_underflow_fn(); }
    }

    #[test]
    fn test_cat_b_03_mul_overflow() {
        unsafe { cat_b_03_mul_overflow_fn(); }
    }

    #[test]
    fn test_cat_b_04_shl_bitwidth() {
        unsafe { cat_b_04_shl_bitwidth_fn(); }
    }

    #[test]
    fn test_cat_b_05_shr_negative() {
        unsafe { cat_b_05_shr_negative_fn(); }
    }

    #[test]
    fn test_cat_b_06_null_deref() {
        unsafe { cat_b_06_null_deref_fn(); }
    }

    #[test]
    fn test_cat_b_07_use_after_free() {
        unsafe { cat_b_07_use_after_free_fn(); }
    }

    #[test]
    fn test_cat_b_08_double_free() {
        unsafe { cat_b_08_double_free_fn(); }
    }

    #[test]
    fn test_cat_b_09_uninit_read() {
        unsafe { cat_b_09_uninit_read_fn(); }
    }

    #[test]
    fn test_cat_b_10_out_of_bounds() {
        unsafe { cat_b_10_out_of_bounds_fn(); }
    }

    // Known Open Issues
    #[test]
    fn test_cat_c_01_issue_947() {
        unsafe { cat_c_01_issue_947_fn(); }
    }

    #[test]
    fn test_cat_c_02_issue_685() {
        unsafe { cat_c_02_issue_685_fn(); }
    }
}
