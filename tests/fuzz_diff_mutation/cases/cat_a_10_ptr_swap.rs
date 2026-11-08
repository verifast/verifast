// verifast_options{skip_specless_fns}
pub unsafe fn test_ptr_swap(a: *mut i32, b: *mut i32)
//@ req *a |-> ?va &*& *b |-> ?vb;
//@ ens *a |-> vb &*& *b |-> va;
{
    let tmp = *a;
    *a = *b;
    *b = tmp;
}
fn main() {}
