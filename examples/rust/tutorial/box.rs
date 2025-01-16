use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

pub struct Box<T> {
    ptr: *mut T,
}

/*@
pred<T> <Box<T>>.own(t, b) = *b.ptr |-> ?v &*& <T>.own(t, v) &*& std::alloc::alloc_block(b.ptr as *u8, std::alloc::Layout::new_::<T>());

pred_ctor field_ptr_chunk<T>(l: *Box<T>, p: *T)(;) = (*l).ptr |-> p;
pred<T> <Box<T>>.share(k, t, l) = [_]exists(?p) &*& [_]frac_borrow(k, field_ptr_chunk(l, p)) &*& [_](<T>.share)(k, t, p);

lem Box_share_mono<T>(k: lifetime_t, k1: lifetime_t, t: thread_id_t, l: *Box<T>)
    req type_interp::<T>() &*& lifetime_inclusion(k1, k) == true &*& [_](<Box<T>>.share)(k, t, l);
    ens type_interp::<T>() &*& [_](<Box<T>>.share)(k1, t, l);
{
    // We use the monotonicity of `frac_borrow` and `<T>.share` predicate
    open <Box<T>>.share(k, t, l);
    assert [_]exists(?p);
    frac_borrow_mono(k, k1, field_ptr_chunk(l, p));
    share_mono(k, k1, t, p);
    close <Box<T>>.share(k1, t, l);
    leak <Box<T>>.share(k1, t, l);
}

lem Box_share_full<T>(k: lifetime_t, t: thread_id_t, l: *Box<T>)
    req type_interp::<T>() &*& atomic_mask(Nlft) &*& [?q]lifetime_token(k) &*& full_borrow(k, <Box<T>>.full_borrow_content(t, l));
    ens type_interp::<T>() &*& atomic_mask(Nlft) &*& [q]lifetime_token(k) &*& [_](<Box<T>>.share)(k, t, l);
{
    // We convert `full_borrow(k, <Box<T>>.full_borrow_content(t, l))` to `full_borrow(k, (*l).ptr |-> p &*& <T>.full_borrow_content(t, p));
    let klong = open_full_borrow_strong_m(k, <Box<T>>.full_borrow_content(t, l), q);
    open <Box<T>>.full_borrow_content(t, l)();
    open Box_own::<T>(t, ?b);
    let p = b.ptr;
    close_full_borrow_content::<T>(t, p);
    close field_ptr_chunk::<T>(l, p)();
    close sep(field_ptr_chunk(l, p), (<T>.full_borrow_content)(t, p))();
    {
    pred ctx(;) = std::alloc::alloc_block(p as *u8, std::alloc::Layout::new_::<T>());
    close ctx();
    produce_lem_ptr_chunk full_borrow_convert_strong(ctx, sep(field_ptr_chunk(l, p), (<T>.full_borrow_content)(t, p)), klong, <Box<T>>.full_borrow_content(t, l))() {
        open ctx();
        open sep(field_ptr_chunk(l, p), (<T>.full_borrow_content)(t, p))();
        open field_ptr_chunk::<T>(l, p)();
        open_full_borrow_content::<T>(t, p);
        close <Box<T>>.own(t, b);
        close <Box<T>>.full_borrow_content(t, l)();
    }{
        close_full_borrow_strong_m(klong, <Box<T>>.full_borrow_content(t, l), sep(field_ptr_chunk(l, p), (<T>.full_borrow_content)(t, p)));
    }
    }//ctx
    full_borrow_mono(klong, k, sep(field_ptr_chunk(l, p), (<T>.full_borrow_content)(t, p)));
    full_borrow_split_m(k, field_ptr_chunk(l, p), (<T>.full_borrow_content)(t, p));
    full_borrow_into_frac_m(k, field_ptr_chunk(l, p));
    share_full_borrow_m::<T>(k, t, p);
    leak exists(p);
    close <Box<T>>.share(k, t, l);
    leak <Box<T>>.share(k, t, l);
}

lem init_ref_Box<T>(p: *Box<T>)
    req type_interp::<T>() &*& atomic_mask(Nlft) &*& ref_init_perm(p, ?x) &*& [_]Box_share::<T>(?k, ?t, x) &*& [?q]lifetime_token(k);
    ens type_interp::<T>() &*& atomic_mask(Nlft) &*& [q]lifetime_token(k) &*& [_]Box_share::<T>(k, t, p) &*& [_]frac_borrow(k, ref_initialized_(p));
{
    assume(false); // TODO
}
@*/

impl<T> Box<T> {
    pub fn new(v: T) -> Box<T> {
        let l = Layout::new::<T>();
        if l.size() == 0 {
            std::process::abort();
        }
        unsafe {
            let p = alloc(l) as *mut T;
            if p.is_null() {
                handle_alloc_error(l);
            }
            //@ from_u8s_(p);
            std::ptr::write(p, v);
            let r = Self { ptr: p };
            //@ close <Box<T>>.own(_t, r);
            r
        }
    }
}

impl<T> Drop for Box<T> {
    fn drop<'a>(&'a mut self)
    //@ req thread_token(?t) &*& <Box<T>>.full_borrow_content(t, self)();
    //@ ens thread_token(t) &*& (*self).ptr |-> ?_;
    {
        unsafe {
            //@ open <Box<T>>.full_borrow_content(t, self)();
            //@ open <Box<T>>.own(t, *self);
            std::ptr::drop_in_place(self.ptr);
            //@ to_u8s_((*self).ptr);
            dealloc(self.ptr as *mut u8, Layout::new::<T>());
        }
    }
}

impl<T> std::ops::Deref for Box<T> {
    type Target = T;
    fn deref<'a>(&'a self) -> &'a T
    //@ req thread_token(?_t) &*& [?_q_a]lifetime_token('a) &*& [_](<Box<T>>.share)('a, _t, self);
    //@ ens thread_token(_t) &*& [_q_a]lifetime_token('a) &*& [_](<T>.share('a, _t, result));
    {
        //@ open <Box<T>>.share('a, _t, self);
        //@ assert [_]exists(?p);
        //@ open_frac_borrow('a, field_ptr_chunk(self, p), _q_a);
        //@ open [?qp]field_ptr_chunk::<T>(self, p)();
        let r = unsafe { &*self.ptr };
        //@ close [qp]field_ptr_chunk::<T>(self, p)();
        //@ close_frac_borrow(qp, field_ptr_chunk(self, p));
        r
    }
}

impl<T> std::ops::DerefMut for Box<T> {
    fn deref_mut<'a>(&'a mut self) -> &'a mut T {
        unsafe {
            //@ open_full_borrow_strong_('a, <Box<T>>.full_borrow_content(_t, self));
            //@ open <Box<T>>.full_borrow_content(_t, self)();
            //@ open <Box<T>>.own(_t, ?b);
            let r = &mut *self.ptr;
            /*@
            {
                pred ctx(;) = (*self).ptr |-> r &*& std::alloc::alloc_block(r as *u8, std::alloc::Layout::new_::<T>());
                produce_lem_ptr_chunk restore_full_borrow_(ctx, <T>.full_borrow_content(_t, r), <Box<T>>.full_borrow_content(_t, self))() {
                    open ctx();
                    open_full_borrow_content::<T>(_t, r);
                    close <Box<T>>.own(_t, b);
                    close <Box<T>>.full_borrow_content(_t, self)();
                }{
                    close ctx();
                    close_full_borrow_content::<T>(_t, r);
                    close_full_borrow_strong_();
                }
            }
            @*/
            r
        }
    }
}

unsafe impl<T: Send> Send for Box<T> {}
/*@
lem Box_send<T>(t1: thread_id_t)
    req type_interp::<T>() &*& <Box<T>>.own(?t, ?b) &*& is_Send(typeid(T)) == true;
    ens type_interp::<T>() &*& <Box<T>>.own(t1, b);
{
    open <Box<T>>.own(t, b);
    assert *b.ptr |-> ?v;
    Send::send(t, t1, v);
    close <Box<T>>.own(t1, b);
}
@*/

unsafe impl<T: Sync> Sync for Box<T> {}
/*@
lem Box_sync<T>(t1: thread_id_t)
    req type_interp::<T>() &*& [_](<Box<T>>.share(?k, ?t, ?l)) &*& is_Sync(typeid(T)) == true;
    ens type_interp::<T>() &*& [_](<Box<T>>.share(k, t1, l));
{
    open <Box<T>>.share(k, t, l);
    assert [_]exists(?p);
    Sync::sync(k, t, t1, p);
    close <Box<T>>.share(k, t1, l);
    leak <Box<T>>.share(k, t1, l);
}
@*/
