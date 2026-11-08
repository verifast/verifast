// verifast_options{skip_specless_fns}
pub unsafe fn probe_storage_dead() -> i32
//@ req true;
//@ ens true;
{
    let p: *mut i32;
    {
        let mut x: i32 = 42;
        p = &raw mut x;
        *p = 100;
    }
    *p
}
fn main() {}
