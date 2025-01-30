use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};
//@ use std::alloc_block_;

pub struct BoxU8 { ptr: *mut u8 }
//@ pred BoxU8(b: BoxU8, v: u8) = *b.ptr |-> v;

impl BoxU8 {
pub unsafe fn get1(this: *const BoxU8) -> u8
//@ req [?qb](*this |-> ?b) &*& [?qv]BoxU8(b, ?v);
//@ ens [qb](*this |-> b) &*& [qv]BoxU8(b, v) &*& result == v;
{
    //@ open BoxU8(b, v);
    let r = *(*this).ptr;
    //@ close [qv]BoxU8(b, v);
    r
}

pub unsafe fn set1(this: *mut BoxU8, new: u8)
//@ req [?qb](*this |-> ?b) &*& BoxU8(b, _);
//@ ens [qb](*this |-> b) &*& BoxU8(b, new);
{
    //@ open BoxU8(b, _);
    *(*this).ptr = new;
    //@ close BoxU8(b, new);
}
} // impl BoxU8

/*@
pred BoxU8_(b: BoxU8; v: u8) = *b.ptr |-> v;
pred BoxU8_own_(b: BoxU8; v: u8) = BoxU8_(b, v) &*& alloc_block_(b.ptr);
@*/

impl BoxU8 {

pub unsafe fn new(v: u8) -> BoxU8
//@ req true;
//@ ens BoxU8_own_(result, v);
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
//@ req BoxU8_own_(this, ?_);
//@ ens true;
{
    //@ to_u8s_(this.ptr);
    dealloc(this.ptr, Layout::new::<u8>());
}

pub unsafe fn get(this: *const BoxU8) -> u8
//@ req [?qb](*this |-> ?b) &*& [?qv]BoxU8_(b, ?v);
//@ ens [qb](*this |-> b) &*& [qv]BoxU8_(b, v) &*& result == v;
{ *(*this).ptr }

pub unsafe fn set(this: *mut BoxU8, new: u8)
//@ req [?qb](*this |-> ?b) &*& BoxU8_(b, _);
//@ ens [qb](*this |-> b) &*& BoxU8_(b, new);
{ *(*this).ptr = new; }

} // impl BoxU8

impl BoxU8 {
    pub unsafe fn from_raw(raw: *mut u8) -> BoxU8
    //@ req *raw |-> ?v &*& std::alloc::alloc_block(raw, std::alloc::Layout::new_::<u8>());
    //@ ens BoxU8_own_(result, v);
    {
        Self { ptr: raw }
    }

    pub unsafe fn into_raw(this: BoxU8) -> *mut u8
    //@ req BoxU8_own_(this, ?v);
    //@ ens *result |-> v &*& std::alloc::alloc_block(result, std::alloc::Layout::new_::<u8>());
    {
        this.ptr
    }
}