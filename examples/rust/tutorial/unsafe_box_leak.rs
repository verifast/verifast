use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};
//@ use std::alloc_block_;

pub struct Box<T> { ptr: *mut T }
//@ pred Box_own_<T>(b: Box<T>; v: T) = *b.ptr |-> v &*& alloc_block_(b.ptr);

impl<T> Box<T> {
pub unsafe fn new(v: T) -> Box<T>
//@ req std::mem::size_of_::<T> >= 1;
//@ ens Box_own_(result, v);
{
    let l = Layout::new::<T>();
    let p = alloc(l) as *mut T;
    if p.is_null() { handle_alloc_error(l) }
    //@ from_u8s_(p);
    p.write(v);
    Self { ptr: p }
}

pub unsafe fn drop(this: Box<T>)
//@ req Box_own_(this, _);
//@ ens true;
{
    //@ to_u8s_(this.ptr);
    // `v` never gets destructed!
    dealloc(this.ptr as *mut u8, Layout::new::<T>());
}

pub unsafe fn set(this: *mut Box<T>, new: T)
//@ req [?qb](*this |-> ?b) &*& Box_own_(b, _);
//@ ens [qb](*this |-> b) &*& Box_own_(b, new);
{ (*this).ptr.write(new) }

pub unsafe fn replace(this: *const Box<T>, new: T) -> T
//@ req [?qb](*this |-> ?b) &*& Box_own_(b, ?old_);
//@ ens [qb](*this |-> b) &*& Box_own_(b, new) &*& result == old_;
{
    let old = (*this).ptr.read();
    (*this).ptr.write(new);
    old
}

} // impl<T> Box<T>

impl<T: Copy> Box<T> {
pub unsafe fn get(this: *const Box<T>) -> T
//@ req [?qb](*this |-> ?b) &*& [?qv]Box_own_(b, ?v);
//@ ens [qb](*this |-> b) &*& [qv]Box_own_(b, v) &*& result == v;
{ (*this).ptr.read() }
} // impl<T: Copy> Box<T>

impl<T> Box<T> {
    pub unsafe fn from_raw(raw: *mut T) -> Box<T>
//@ req *raw |-> ?v &*& std::alloc::alloc_block(raw as *u8, std::alloc::Layout::new_::<T>());
//@ ens Box_own_(result, v);
    {
        Self { ptr: raw }
    }

    pub unsafe fn into_raw(this: Box<T>) -> *mut T
//@ req Box_own_(this, ?v);
//@ ens *result |-> v &*& std::alloc::alloc_block(result as *u8, std::alloc::Layout::new_::<T>());
    {
        this.ptr
    }
}
