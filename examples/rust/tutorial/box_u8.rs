use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

pub struct BoxU8 {
    ptr: *mut u8,
}

/*@
pred <BoxU8>.own(t, b;) = *(b.ptr) |-> ?_ &*& std::alloc::alloc_block(b.ptr, std::alloc::Layout::new_::<u8>());
pred_ctor field_ptr_chunk(l: *BoxU8, p: *u8)(;) = (*l).ptr |-> p;
pred <BoxU8>.share(k, t, l) = [_]exists(?p) &*& [_]frac_borrow(k, field_ptr_chunk(l, p)) &*& [_]frac_borrow(k, u8_full_borrow_content(t, p));

lem BoxU8_share_mono(k: lifetime_t, k1: lifetime_t, t: thread_id_t, l: *BoxU8)
    req lifetime_inclusion(k1, k) == true &*& [_]BoxU8_share(k, t, l);
    ens [_]BoxU8_share(k1, t, l);
{
    open BoxU8_share(k, t, l);
    assert [_]exists(?p);
    frac_borrow_mono(k, k1, field_ptr_chunk(l, p));
    frac_borrow_mono(k, k1, u8_full_borrow_content(t, p));
    close BoxU8_share(k1, t, l);
    leak BoxU8_share(k1, t, l);
}

pred_ctor ctx(p: *u8)(;) = std::alloc::alloc_block(p, std::alloc::Layout::new_::<u8>());
lem BoxU8_share_full(k: lifetime_t, t: thread_id_t, l: *BoxU8)
    req atomic_mask(Nlft) &*& [?q]lifetime_token(k) &*& full_borrow(k, BoxU8_full_borrow_content(t, l));
    ens atomic_mask(Nlft) &*& [q]lifetime_token(k) &*& [_]BoxU8_share(k, t, l);
{
    let klong = open_full_borrow_strong_m(k, BoxU8_full_borrow_content(t, l), q);
    open BoxU8_full_borrow_content(t, l)();
    open BoxU8_own(t, ?b);
    let p = b.ptr;
    close sep(field_ptr_chunk(l, p), u8_full_borrow_content(t, p))();
    produce_lem_ptr_chunk full_borrow_convert_strong(ctx(p), sep(field_ptr_chunk(l, p), u8_full_borrow_content(t, p)), klong, BoxU8_full_borrow_content(t, l))() {
        open sep(field_ptr_chunk(l, p), u8_full_borrow_content(t, p))();
        close BoxU8_own(t, b);
        close BoxU8_full_borrow_content(t, l)();
    }{
        close_full_borrow_strong_m(klong, BoxU8_full_borrow_content(t, l), sep(field_ptr_chunk(l, p), u8_full_borrow_content(t, p)));
    }
    full_borrow_mono(klong, k, sep(field_ptr_chunk(l, p), u8_full_borrow_content(t, p)));
    full_borrow_split_m(k, field_ptr_chunk(l, p), u8_full_borrow_content(t, p));
    full_borrow_into_frac_m(k, field_ptr_chunk(l, p));
    full_borrow_into_frac_m(k, u8_full_borrow_content(t, p));
    leak exists(p);
    close BoxU8_share(k, t, l);
    leak BoxU8_share(k, t, l);
}

lem init_ref_BoxU8(p: *BoxU8)
    req atomic_mask(Nlft) &*& ref_init_perm(p, ?x) &*& [_]BoxU8_share(?k, ?t, x) &*& [?q]lifetime_token(k);
    ens atomic_mask(Nlft) &*& [q]lifetime_token(k) &*& [_]BoxU8_share(k, t, p) &*& [_]frac_borrow(k, ref_initialized_(p));
{
    assume(false); // TODO
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
    //@ ens thread_token(t) &*& (*self).ptr |-> ?_;
    {
        unsafe {
            //@ open BoxU8_full_borrow_content(t, self)();
            //@ assert (*self).ptr |-> ?p;
            //@ to_u8s_(p);
            dealloc(self.ptr as *mut u8, Layout::new::<u8>());
        }
    }
}

impl std::ops::Deref for BoxU8 {
    type Target = u8;
    fn deref<'a>(&'a self) -> &'a u8 {
        //@ open BoxU8_share('a, _t, self);
        //@ assert [_]exists(?p);
        //@ open_frac_borrow('a, field_ptr_chunk(self, p), _q_a);
        //@ assert [?qp]field_ptr_chunk(self, p)();
        let r = unsafe { &*self.ptr };
        //@ close_frac_borrow(qp, field_ptr_chunk(self, p));
        r
    }
}

impl std::ops::DerefMut for BoxU8 {
    fn deref_mut<'a>(&'a mut self) -> &'a mut u8 {
        //@ let klong = open_full_borrow_strong('a, BoxU8_full_borrow_content(_t, self), _q_a);
        //@ open BoxU8_full_borrow_content(_t, self)();
        let r = unsafe { &mut *self.ptr };
        //@ open BoxU8_own(_t, ?b);
        //@ let p = b.ptr;
        //@ close sep(field_ptr_chunk(self, p), u8_full_borrow_content(_t, p))();
        /*@
        produce_lem_ptr_chunk full_borrow_convert_strong(ctx(p), sep(field_ptr_chunk(self, p), u8_full_borrow_content(_t, p)), klong, BoxU8_full_borrow_content(_t, self))() {
            open sep(field_ptr_chunk(self, p), u8_full_borrow_content(_t, p))();
            close BoxU8_own(_t, b);
            close BoxU8_full_borrow_content(_t, self)();
        }{
            close_full_borrow_strong(klong, BoxU8_full_borrow_content(_t, self), sep(field_ptr_chunk(self, p), u8_full_borrow_content(_t, p)));
        }
        @*/
        //@ full_borrow_mono(klong, 'a, sep(field_ptr_chunk(self, p), u8_full_borrow_content(_t, p)));
        //@ full_borrow_split('a, field_ptr_chunk(self, p), u8_full_borrow_content(_t, p));
        //@ leak full_borrow('a, field_ptr_chunk(self, p));
        r
    }
}
