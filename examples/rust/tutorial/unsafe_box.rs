use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};
//@ use std::alloc_block_;

pub struct Box<T> { ptr: *mut T }
//@ pred Box_own_<T>(t: thread_id_t, b: Box<T>, v: T) = *b.ptr |-> v &*& <T>.own(t, v) &*& alloc_block_(b.ptr);

impl<T> Box<T> {

pub unsafe fn new(v: T) -> Box<T>
//@ req thread_token(?t) &*& <T>.own(t, v) &*& std::mem::size_of_::<T> >= 1;
//@ ens thread_token(t) &*& Box_own_(t, result, v);
{
    let l = Layout::new::<T>();
    let p = alloc(l) as *mut T;
    if p.is_null() {
        handle_alloc_error(l)
    }
    //@ from_u8s_(p);
    p.write(v);
    let r = Self { ptr: p };
    //@ close Box_own_(t, r, v);
    r
}

pub unsafe fn drop(this: Box<T>)
//@ req thread_token(?t) &*& Box_own_(t, this, _);
//@ ens thread_token(t);
{
    //@ open Box_own_(t, this, _);
    std::ptr::drop_in_place(this.ptr);
    //@ to_u8s_(this.ptr);
    dealloc(this.ptr as *mut u8, Layout::new::<T>());
}

pub unsafe fn replace(this: *const Box<T>, new: T) -> T
//@ req [?qb](*this |-> ?b) &*& Box_own_(?t, b, ?old_) &*& <T>.own(t, new);
//@ ens [qb](*this |-> b) &*& Box_own_(t, b, new) &*& <T>.own(t, old_) &*& result == old_;
{
    //@ open Box_own_(t, b, old_);
    let old = (*this).ptr.read();
    (*this).ptr.write(new);
    //@ close Box_own_(t, b, new);
    old
}

pub unsafe fn set(this: *mut Box<T>, new: T)
//@ req thread_token(?t) &*& [?qb](*this |-> ?b) &*& Box_own_(t, b, _) &*& <T>.own(t, new);
//@ ens thread_token(t) &*& [qb](*this |-> b) &*& Box_own_(t, b, new);
{
    //@ open Box_own_(t, b, _);
    *(*this).ptr = new;
    //@ close Box_own_(t, b, new);
}

} // impl<T> Box<T>

impl<T: Copy> Box<T> {
pub unsafe fn get(this: *const Box<T>) -> T
//@ req [?qb](*this |-> ?b) &*& [?qv]Box_own_(?t, b, ?v);
//@ ens [qb](*this |-> b) &*& [qv]Box_own_(t, b, v) &*& result == v;
{
    //@ open Box_own_(t, b, v);
    let r = *(*this).ptr;
    //@ close [qv]Box_own_(t, b, v);
    r
}
} // impl<T: Copy> Box<T>

impl<T> Box<T> {
    pub unsafe fn from_raw(raw: *mut T) -> Box<T>
    //@ req thread_token(?t) &*& *raw |-> ?v &*& <T>.own(t, v) &*& std::alloc::alloc_block(raw as *u8, std::alloc::Layout::new_::<T>());
    //@ ens thread_token(t) &*& Box_own_(t, result, v);
    {
        let r = Self { ptr: raw };
        //@ close Box_own_(t, r, v);
        r
    }

    pub unsafe fn into_raw(this: Box<T>) -> *mut T
    //@ req thread_token(?t) &*& Box_own_(t, this, ?v);
    //@ ens thread_token(t) &*& *result |-> v &*& <T>.own(t, v) &*& std::alloc::alloc_block(result as *u8, std::alloc::Layout::new_::<T>());
    {
        //@ open Box_own_(t, this, v);
        this.ptr
    }
}
