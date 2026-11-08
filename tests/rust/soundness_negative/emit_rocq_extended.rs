// verifast_options{skip_specless_fns}

// Arithmetic addition with verified precondition
pub unsafe fn add_u32(a: u32, b: u32) -> u32
//@ req a + b <= 4294967295;
//@ ens result == a + b;
//@ on_unwind_ens false;
{
    a + b
}

// Pointer swap with verified separation logic permissions
pub unsafe fn swap_u32(p: *mut u32, q: *mut u32)
//@ req *p |-> ?v1 &*& *q |-> ?v2;
//@ ens *p |-> v2 &*& *q |-> v1;
//@ on_unwind_ens false;
{
    let tmp = *p;
    *p = *q;
    *q = tmp;
}

// Conditional branch: maximum of two unsigned integers
pub fn max_u32(x: u32, y: u32) -> u32
//@ req true;
//@ ens if x >= y { result == x } else { result == y };
//@ on_unwind_ens false;
{
    if x >= y {
        x
    } else {
        y
    }
}

// Conditional branch: absolute difference of two unsigned integers
pub fn abs_diff_u32(a: u32, b: u32) -> u32
//@ req true;
//@ ens if a >= b { result == a - b } else { result == b - a };
//@ on_unwind_ens false;
{
    if a >= b {
        a - b
    } else {
        b - a
    }
}

fn main() {}
