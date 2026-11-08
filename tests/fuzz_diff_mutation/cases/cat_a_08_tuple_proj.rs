// verifast_options{skip_specless_fns}
pub unsafe fn test_tuple_projection(p: *mut (i32, i32)) -> i32
//@ req *p |-> ?val &*& 0 <= val.0 &*& val.0 <= 1000 &*& 0 <= val.1 &*& val.1 <= 1000;
//@ ens *p |-> val &*& result == val.0 + val.1;
{
    (*p).0 + (*p).1
}
fn main() {}
