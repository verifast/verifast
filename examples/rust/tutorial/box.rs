use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

pub struct Box<T> {
    ptr: *mut T,
}

/*@
pred<T> <Box<T>>.own(t, b) = *b.ptr |-> ?v &*& <T>.own(t, v);
pred_ctor frac_borrow_content<T>(l: *Box<T>, ptr: *T)(;) = (*l).ptr |-> ptr;
pred<T> <Box<T>>.share(k, t, l) = [_]exists(?ptr) &*& [_]frac_borrow(k, frac_borrow_content(l, ptr)) &*& [_](<T>.share)(k, t, ptr);

lem Box_share_mono<T>(k: lifetime_t, k1: lifetime_t, t: thread_id_t, l: *Box<T>)
    req type_interp::<T>() &*& lifetime_inclusion(k1, k) == true &*& [_](<Box<T>>.share)(k, t, l);
    ens type_interp::<T>() &*& [_](<Box<T>>.share)(k1, t, l);
{
    open Box_share::<T>(k, t, l);
    assert [_]exists(?ptr);
    frac_borrow_mono(k, k1, frac_borrow_content(l, ptr));
    share_mono(k, k1, t, ptr);
    close Box_share::<T>(k1, t, l);
    leak Box_share(k1, t, l);
}

lem Box_share_full<T>(k: lifetime_t, t: thread_id_t, l: *Box<T>)
    req atomic_mask(Nlft) &*& [?q]lifetime_token(k) &*& full_borrow(k, Box_full_borrow_content(t, l));
    ens atomic_mask(Nlft) &*& [q]lifetime_token(k) &*& [_](<Box<T>>.share)(k, t, l);
{
    let klong = open_full_borrow_strong_m(k, BoxU8_full_borrow_content(t, l), q);
    open BoxU8_full_borrow_content(t, l)();
    open BoxU8_own(t, ?ptr);
    close sep(Box_ptr(l, ptr), u8_full_borrow_content(t, ptr))();
    produce_lem_ptr_chunk full_borrow_convert_strong(ctx(l, ptr), sep(Box_ptr(l, ptr), u8_full_borrow_content(t, ptr)), klong, BoxU8_full_borrow_content(t, l))() {
        open sep(Box_ptr(l, ptr), u8_full_borrow_content(t, ptr))();
        close BoxU8_own(t, ptr);
        close BoxU8_full_borrow_content(t, l)();
    }{
        close_full_borrow_strong_m(klong, BoxU8_full_borrow_content(t, l), sep(Box_ptr(l, ptr), u8_full_borrow_content(t, ptr)));
    }
    full_borrow_mono(klong, k, sep(Box_ptr(l, ptr), u8_full_borrow_content(t, ptr)));
    full_borrow_split_m(k, Box_ptr(l, ptr), u8_full_borrow_content(t, ptr));
    full_borrow_into_frac_m(k, Box_ptr(l, ptr));
    full_borrow_into_frac_m(k, u8_full_borrow_content(t, ptr));
    leak exists(ptr);
    close BoxU8_share(k, t, l);
    leak BoxU8_share(k, t, l);
}
@*/

impl<T> Box<T> {
    pub fn new(v: T) -> Box<T> {
        let l = Layout::new::<T>();
        if l.size() == 0 { std::process::abort(); }
        unsafe {
            let p = alloc(l) as *mut T;
            if p.is_null() {
                handle_alloc_error(l);
            }
            //@ from_u8s_(p);
            std::ptr::write(p, v);
            let r = Self { ptr: p };
            //@ close Box_own::<T>(_t, r);
            r
        }
    }
}

impl<T> Drop for Box<T> {
    fn drop<'a>(&'a mut self)
    //@ req thread_token(?t) &*& Box_full_borrow_content::<T>(t, self)();
    //@ ens thread_token(t) &*& (*self).ptr |-> ?_ &*& struct_Box_padding(self);
    {
        unsafe {
            //@ open BoxU8_full_borrow_content(t, self)();
            //@ assert (*self).ptr |-> ?ptr;
            //@ to_u8s_(ptr);
            dealloc(self.ptr as *mut u8, Layout::new::<T>());
        }
    }
}

impl<T> std::ops::Deref for Box<T> {
    type Target = T;
    fn deref<'a>(&'a self) -> &'a T {
        //@ open BoxU8_share(a, _t, self);
        //@ assert [_]exists(?ptr);
        //@ open_frac_borrow(a, Box_ptr(self, ptr), _q_a);
        //@ assert [?qp]Box_ptr(self, ptr)();
        let r = unsafe{ &*self.ptr };
        //@ close_frac_borrow(qp, Box_ptr(self, ptr));
        r
    }
}

impl<T> std::ops::DerefMut for Box<T> {
    fn deref_mut<'a>(&'a mut self) -> &'a mut T {
        //@ let klong = open_full_borrow_strong(a, BoxU8_full_borrow_content(_t, self), _q_a);
        //@ open BoxU8_full_borrow_content(_t, self)();
        let r = unsafe { &mut *self.ptr };
        //@ open BoxU8_own(_t, ?ptr);
        //@ close sep(Box_ptr(self, ptr), u8_full_borrow_content(_t, ptr))();
        /*@
        produce_lem_ptr_chunk full_borrow_convert_strong(ctx(self, ptr), sep(Box_ptr(self, ptr), u8_full_borrow_content(_t, ptr)), klong, BoxU8_full_borrow_content(_t, self))() {
            open sep(Box_ptr(self, ptr), u8_full_borrow_content(_t, ptr))();
            close BoxU8_own(_t, ptr);
            close BoxU8_full_borrow_content(_t, self)();
        }{
            close_full_borrow_strong(klong, BoxU8_full_borrow_content(_t, self), sep(Box_ptr(self, ptr), u8_full_borrow_content(_t, ptr)));
        }
        @*/
        //@ full_borrow_mono(klong, a, sep(Box_ptr(self, ptr), u8_full_borrow_content(_t, ptr)));
        //@ full_borrow_split(a, Box_ptr(self, ptr), u8_full_borrow_content(_t, ptr));
        //@ leak full_borrow(a, Box_ptr(self, ptr));
        r
    }
}