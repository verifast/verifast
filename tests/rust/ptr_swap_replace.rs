// Specifications of `ptr::replace`, `ptr::swap`, `ptr::swap_nonoverlapping` and
// `ptr::slice_from_raw_parts`.
use std::ptr;

unsafe fn replace_u8(p: *mut u8, v: u8) -> u8
//@ req *p |-> ?old;
//@ ens *p |-> v &*& result == old;
{
    ptr::replace(p, v)
}

unsafe fn swap_distinct(x: *mut u8, y: *mut u8)
//@ req *x |-> ?vx &*& *y |-> ?vy;
//@ ens *x |-> vy &*& *y |-> vx;
{
    //@ close std::ptr::swap_second_target::<u8>(false, x, y, vx, vy);
    ptr::swap(x, y);
}

unsafe fn swap_same(x: *mut u8)
//@ req *x |-> ?vx;
//@ ens *x |-> vx;
{
    //@ close std::ptr::swap_second_target::<u8>(true, x, x, vx, vx);
    ptr::swap(x, x);
}

unsafe fn swap_runs(x: *mut u8, y: *mut u8, n: usize)
//@ req x[..n] |-> ?xs &*& y[..n] |-> ?ys;
//@ ens x[..n] |-> ys &*& y[..n] |-> xs;
{
    ptr::swap_nonoverlapping(x, y, n);
}

unsafe fn make_slice(p: *const u8, n: usize) -> *const [u8]
//@ req true;
//@ ens result as *u8 == p &*& result.len() == n;
{
    ptr::slice_from_raw_parts(p, n)
}

fn main() {}
