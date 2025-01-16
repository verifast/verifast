use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};
//@ use std::alloc_block_;

unsafe fn new_u8(v: u8) -> *mut u8
//@ req true;
/*@ ens *result |-> v &*&
alloc_block_(result); @*/
{
    let l = Layout::new::<u8>();
    let p = alloc(l);
    if p.is_null() {
        handle_alloc_error(l);
    }
    *p = v;
    //@ open array_(_, _, _);
    p
}

unsafe fn main()
//@ req true;
//@ ens true;
{
    let p = new_u8(42);
    assert!(*p == 42);
    //@ to_u8s_(p);
    dealloc(p, Layout::new::<u8>());
}
