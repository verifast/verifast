// verifast_options{skip_specless_fns}
pub unsafe fn bad_null() -> i32
//@ req true;
//@ ens true;
{
    let p = 0 as *mut i32;
    *p
}
fn main() {}
