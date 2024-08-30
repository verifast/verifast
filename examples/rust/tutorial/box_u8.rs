use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

pub struct BoxU8 {
    ptr: *mut u8,
}

/*@
pred BoxU8_own(t: thread_id_t, ptr: *u8;) = *ptr |-> ?v_ &*& std::alloc::alloc_block(ptr, std::alloc::Layout::new_::<u8>());
pred_ctor Box_ptr(l: *BoxU8, p: *u8)(;) = (*l).ptr |-> p;
pred BoxU8_share(k: lifetime_t, t: thread_id_t, l: *BoxU8) = [_]exists(?p) &*& [_]frac_borrow(k, Box_ptr(l, p)) &*& [_]frac_borrow(k, u8_full_borrow_content(t, p));

lem BoxU8_share_mono(k: lifetime_t, k1: lifetime_t, t: thread_id_t, l: *BoxU8)
    req lifetime_inclusion(k1, k) == true &*& [_]BoxU8_share(k, t, l);
    ens [_]BoxU8_share(k1, t, l);
{
    open BoxU8_share(k, t, l);
    assert [_]exists(?p);
    frac_borrow_mono(k, k1, Box_ptr(l, p));
    frac_borrow_mono(k, k1, u8_full_borrow_content(t, p));
    close BoxU8_share(k1, t, l);
    leak BoxU8_share(k1, t, l);
}

pred_ctor ctx(l: *BoxU8, ptr: *u8)(;) = struct_BoxU8_padding(l) &*& std::alloc::alloc_block(ptr, std::alloc::Layout::new_::<u8>());
lem BoxU8_share_full(k: lifetime_t, t: thread_id_t, l: *BoxU8)
    req atomic_mask(Nlft) &*& [?q]lifetime_token(k) &*& full_borrow(k, BoxU8_full_borrow_content(t, l));
    ens atomic_mask(Nlft) &*& [q]lifetime_token(k) &*& [_]BoxU8_share(k, t, l);
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

impl BoxU8 {
    pub fn new(v: u8) -> BoxU8 {
        let l = Layout::new::<u8>();
        unsafe {
        let p = alloc(l);
        if p.is_null() {
            handle_alloc_error(l);
        }
        *p = v;
        Self { ptr: p }
        }
    }
}

impl Drop for BoxU8 {
    fn drop<'a>(&'a mut self)
    //@ req thread_token(?t) &*& BoxU8_full_borrow_content(t, self)();
    //@ ens thread_token(t) &*& (*self).ptr |-> ?_ &*& struct_BoxU8_padding(self);
    {
        unsafe {
            //@ open BoxU8_full_borrow_content(t, self)();
            //@ assert (*self).ptr |-> ?ptr;
            //@ to_u8s_(ptr);
            dealloc(self.ptr as *mut u8, Layout::new::<u8>());
        }
    }
}

impl std::ops::Deref for BoxU8 {
    type Target = u8;
    fn deref<'a>(&'a self) -> &'a u8 {
        //@ open BoxU8_share(a, _t, self);
        //@ assert [_]exists(?ptr);
        //@ open_frac_borrow(a, Box_ptr(self, ptr), _q_a);
        //@ assert [?qp]Box_ptr(self, ptr)();
        let r = unsafe{ &*self.ptr };
        //@ close_frac_borrow(qp, Box_ptr(self, ptr));
        r
    }
}

impl std::ops::DerefMut for BoxU8 {
    fn deref_mut<'a>(&'a mut self) -> &'a mut u8 {
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