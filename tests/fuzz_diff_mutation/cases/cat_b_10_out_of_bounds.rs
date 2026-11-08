// verifast_options{skip_specless_fns}
pub unsafe fn bad_oob() -> i32
//@ req true;
//@ ens true;
{
    let mut x: i32 = 42;
    let p = &raw mut x;
    let oob_p = p.add(4);
    *oob_p
}
fn main() {}
