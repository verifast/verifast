// verifast_options{skip_specless_fns}
pub unsafe fn test_raw_ptr() -> i32
//@ req true;
//@ ens result == 42;
{
    let mut x: i32 = 0;
    let p = &raw mut x;
    *p = 42;
    *p
}
fn main() {}
