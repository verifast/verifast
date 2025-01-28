use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};
//@ use std::alloc_block_;

pub struct Box<T> { ptr: *mut T }
//@ pred Box_<T>(b: Box<T>; v: T) = *b.ptr |-> v;
//@ pred Box<T>(t: thread_id_t, b: Box<T>, v: T) = *b.ptr |-> v &*& <T>.own(t, v) &*& alloc_block_(b.ptr);

impl<T> Box<T> {
pub unsafe fn new(v: T) -> Box<T>
//@ req thread_token(?t) &*& <T>.own(t, v) &*& std::mem::size_of_::<T> >= 1;
//@ ens thread_token(t) &*& Box(t, result, v);
{
    let l = Layout::new::<T>();
    let p = alloc(l) as *mut T;
    if p.is_null() {
        handle_alloc_error(l)
    }
    //@ from_u8s_(p);
    std::ptr::write(p, v);
    let r = Self { ptr: p };
    //@ close Box(t, r, v);
    r
}

pub unsafe fn drop(this: Box<T>)
//@ req thread_token(?t) &*& Box(t, this, _);
//@ ens thread_token(t);
{
    //@ open Box(t, this, _);
    std::ptr::drop_in_place(this.ptr);
    //@ to_u8s_(this.ptr);
    dealloc(this.ptr as *mut u8, Layout::new::<T>());
}

} // impl<T> Box<T>

impl<T: Copy> Box<T> {

pub unsafe fn get(this: *const Box<T>) -> T
//@ req [?qb](*this |-> ?b) &*& [?qv]Box_(b, ?v);
//@ ens [qb](*this |-> b) &*& [qv]Box_(b, v) &*& result == v;
{ *(*this).ptr }

pub unsafe fn set(this: *const Box<T>, new: T)
//@ req [?qb](*this |-> ?b) &*& Box_(b, _);
//@ ens [qb](*this |-> b) &*& Box_(b, new);
{ *(*this).ptr = new }

} // impl<T: Copy> Box<T>

impl<T> Box<T> {
    pub unsafe fn from_raw(raw: *mut T) -> Box<T>
    //@ req thread_token(?t) &*& *raw |-> ?v &*& <T>.own(t, v) &*& std::alloc::alloc_block(raw as *u8, std::alloc::Layout::new_::<T>());
    //@ ens thread_token(t) &*& Box(t, result, v);
    {
        let r = Self { ptr: raw };
        //@ close Box(t, r, v);
        r
    }

    pub unsafe fn into_raw(this: Box<T>) -> *mut T
    //@ req thread_token(?t) &*& Box(t, this, ?v);
    //@ ens thread_token(t) &*& *result |-> v &*& <T>.own(t, v) &*& std::alloc::alloc_block(result as *u8, std::alloc::Layout::new_::<T>());
    {
        //@ open Box(t, this, v);
        this.ptr
    }
}
