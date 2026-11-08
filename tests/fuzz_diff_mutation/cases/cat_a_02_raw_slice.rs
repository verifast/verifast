// verifast_options{skip_specless_fns}
pub struct RawSlice {
    pub v: *mut [i32],
    pub n: usize,
}

pub unsafe fn test_raw_slice_field(s: *mut RawSlice, w: *mut [i32]) -> *mut [i32]
//@ req (*s).v |-> ?v0;
//@ ens (*s).v |-> w &*& result == v0;
{
    let old = (*s).v;
    (*s).v = w;
    old
}
fn main() {}
