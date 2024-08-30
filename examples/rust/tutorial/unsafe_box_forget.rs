use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

pub struct Box<T> {
    ptr: *mut T,
}

//@ pred Box<T>(b: Box<T>; v: T) = *b.ptr |-> v &*& std::alloc::alloc_block(b.ptr as *u8, std::alloc::Layout::new_::<T>());

impl<T> Box<T> {
    pub unsafe fn new(v: T) -> Box<T>
    //@ req std::mem::size_of_::<T> >= 1;
    //@ ens Box(result, v);
    {
        let l = Layout::new::<T>();
        let p = alloc(l) as *mut T;
        if p.is_null() {
            handle_alloc_error(l)
        }
        //@ from_u8s_(p);
        std::ptr::write(p, v);
        Self { ptr: p }
    }

    pub unsafe fn drop(this: Box<T>)
    //@ req Box(this, ?v_);
    //@ ens true;
    {
        //@ to_u8s_(this.ptr);
        // `v` never gets destructed!
        dealloc(this.ptr as *mut u8, Layout::new::<T>());
    }

    pub unsafe fn from_raw(raw: *mut T) -> Box<T>
    //@ req *raw |-> ?v &*& std::alloc::alloc_block(raw as *u8, std::alloc::Layout::new_::<T>());
    //@ ens Box(result, v);
    {
        Self { ptr: raw }
    }

    pub unsafe fn into_raw(this: Box<T>) -> *mut T
    //@ req Box(this, ?v);
    //@ ens *result |-> v &*& std::alloc::alloc_block(result as *u8, std::alloc::Layout::new_::<T>());
    {
        this.ptr
    }
}
