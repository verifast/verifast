use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};
//@ use std::alloc_block_;

pub struct BoxU8 { ptr: *mut u8 }

impl BoxU8 {

pub unsafe fn new(v: u8) -> BoxU8
//@ req true;
/*@ ens *result.ptr |-> v &*&
alloc_block_(result.ptr); @*/
{
    let l = Layout::new::<u8>();
    let p = alloc(l);
    if p.is_null() {
        handle_alloc_error(l);
    }
    *p = v;
    Self { ptr: p }
}

pub unsafe fn drop(this: BoxU8)
/*@ req *this.ptr |-> _ &*&
alloc_block_(this.ptr); @*/
//@ ens true;
{
    //@ to_u8s_(this.ptr);
    dealloc(this.ptr, Layout::new::<u8>());
}

pub unsafe fn get(p: *const BoxU8) -> u8
//@ req [?qb](*p |-> ?b) &*& [?qv](*b.ptr |-> ?v);
/*@ ens [qb](*p |-> b) &*&
[qv](*b.ptr |-> v) &*& result == v; @*/
{ *(*p).ptr }

pub unsafe fn set(p: *mut BoxU8, new: u8)
//@ req [?qb](*p |-> ?b) &*& *b.ptr |-> _;
//@ ens [qb](*p |-> b) &*& *b.ptr |-> new;
{ *(*p).ptr = new; }

} // impl BoxU8

impl BoxU8 {
pub unsafe fn get1(p: *const BoxU8) -> u8
//@ req [1/2](*p |-> ?b) &*& [1/3](*b.ptr |-> ?v);
//@ ens [1/2](*p |-> b) &*& [1/3](*b.ptr |-> v) &*& result == v;
{ *(*p).ptr }
}

impl BoxU8 {
pub unsafe fn from_raw(raw: *mut u8) -> BoxU8
//@ req *raw |-> ?v &*& std::alloc::alloc_block(raw, std::alloc::Layout::new_::<u8>());
//@ ens *result.ptr |-> v &*& std::alloc::alloc_block(result.ptr, std::alloc::Layout::new_::<u8>());
{
    Self { ptr: raw }
}

pub unsafe fn into_raw(this: BoxU8) -> *mut u8
//@ req *this.ptr |-> ?v &*& std::alloc::alloc_block(this.ptr, std::alloc::Layout::new_::<u8>());
//@ ens *result |-> v &*& std::alloc::alloc_block(result, std::alloc::Layout::new_::<u8>());
{
    this.ptr
}
}

unsafe fn main()
//@ req true;
//@ ens true;
{
    let mut b = BoxU8::new(0);
    let p = &mut b as *mut BoxU8;
    assert!(BoxU8::get(p) == 0);
    BoxU8::set(p, 42);
    assert!(BoxU8::get(p) == 42);
    BoxU8::drop(b);
}
