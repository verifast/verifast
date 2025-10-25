use std::alloc::{dealloc, Layout};
//@ use std::alloc_block_;

pub struct BoxU8 { ptr: *mut u8 }

//@ pred <BoxU8>.own(t, b;) = *b.ptr |-> ?_ &*& alloc_block_(b.ptr);

impl BoxU8 {
pub fn into_inner1(b: BoxU8) -> u8 { //| Assuming BoxU8 does not implement destructor
    unsafe {
        let ret = *b.ptr;
        //@ to_u8s_(b.ptr);
        dealloc(b.ptr, Layout::new::<u8>());
        ret
    }
}
} // impl BoxU8
