// verifast_options{skip_specless_fns}
pub unsafe fn probe_aliasing_sb() -> i32
//@ req true;
//@ ens true;
{
    let mut x: i32 = 10;
    let raw_ptr = &raw mut x;
    let ref_mut = &mut *raw_ptr;
    *ref_mut = 20;
    let val = *raw_ptr;
    *ref_mut = 30;
    val
}
fn main() {}
