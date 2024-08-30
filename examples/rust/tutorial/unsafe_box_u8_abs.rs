use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

pub struct BoxU8 {
    ptr: *mut u8,
}
/*@
pred BoxU8(b: BoxU8; v: u8) = *b.ptr |-> v &*& std::alloc::alloc_block(b.ptr, std::alloc::Layout::new_::<u8>()) &*&
    object_pointer_within_limits(b.ptr, 1) == true;
@*/
impl BoxU8 {
    pub unsafe fn new(v: u8) -> BoxU8
    //@ req true;
    //@ ens BoxU8(result, v);
    {
        let l = Layout::new::<u8>();
        let p = alloc(l);
        if p.is_null() {
            handle_alloc_error(l)
        }
        *p = v;
        Self { ptr: p }
    }

    pub unsafe fn drop(this: BoxU8)
    //@ req BoxU8(this, ?v_);
    //@ ens true;
    {
        dealloc(this.ptr, Layout::new::<u8>());
    }

    pub unsafe fn from_raw(raw: *mut u8) -> BoxU8
    //@ req *raw |-> ?v &*& std::alloc::alloc_block(raw, std::alloc::Layout::new_::<u8>()) &*& object_pointer_within_limits(raw, 1) == true;
    //@ ens BoxU8(result, v);
    {
        Self { ptr: raw }
    }

    pub unsafe fn into_raw(this: BoxU8) -> *mut u8
    //@ req BoxU8(this, ?v);
    //@ ens *result |-> v &*& std::alloc::alloc_block(result, std::alloc::Layout::new_::<u8>()) &*& object_pointer_within_limits(result, 1) == true;
    {
        this.ptr
    }
}
