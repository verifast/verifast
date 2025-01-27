// verifast_options{ignore_ref_creation}

/*@
pred<T> <ptr::NonNull<T>>.own(t, nonNull;) = nonNull.pointer as usize != 0;

lem ptr::NonNull_own_mono<T0, T1>()
    req type_interp::<T0>() &*& type_interp::<T1>() &*& ptr::NonNull_own::<T0>(?t, ?v) &*& is_subtype_of::<T0, T1>() == true;
    ens type_interp::<T0>() &*& type_interp::<T1>() &*& ptr::NonNull_own::<T1>(t, ptr::NonNull::<T1> { pointer: v.pointer as *_ });
{
    open ptr::NonNull_own::<T0>(t, v);
    close ptr::NonNull_own::<T1>(t, ptr::NonNull::<T1> { pointer: v.pointer as *_ });
}

pred_ctor ptr::NonNull_frac_bc<T>(t: thread_id_t, l: *ptr::NonNull<T>)(;) = (*l).pointer |-> ?p &*& struct_ptr::NonNull_padding(l) &*& ptr::NonNull_own(t, ptr::NonNull::<T> { pointer: p });
pred<T> <ptr::NonNull<T>>.share(k, t, l) =
    frac_borrow(k, ptr::NonNull_frac_bc(t, l));

lem ptr::NonNull_share_mono<T>(k: lifetime_t, k1: lifetime_t, t: thread_id_t, l: *ptr::NonNull<T>)
    req lifetime_inclusion(k1, k) == true &*& [_]ptr::NonNull_share(k, t, l);
    ens [_]ptr::NonNull_share(k1, t, l);
{
    open <ptr::NonNull<T>>.share(k, t, l);
    frac_borrow_mono(k, k1, ptr::NonNull_frac_bc(t, l));
    assert [?q]frac_borrow(k1, _);
    close [q]<ptr::NonNull<T>>.share(k1, t, l);
}

lem ptr::NonNull_share_full<T>(k: lifetime_t, t: thread_id_t, l: *ptr::NonNull<T>)
    req atomic_mask(MaskTop) &*& full_borrow(k, ptr::NonNull_full_borrow_content(t, l)) &*& [?q]lifetime_token(k);
    ens atomic_mask(MaskTop) &*& [_]ptr::NonNull_share(k, t, l) &*& [q]lifetime_token(k);
{
    produce_lem_ptr_chunk implies(ptr::NonNull_frac_bc(t, l), ptr::NonNull_full_borrow_content(t, l))(){
        open ptr::NonNull_frac_bc::<T>(t, l)();
        close ptr::NonNull_full_borrow_content::<T>(t, l)();
    }{
        produce_lem_ptr_chunk implies(ptr::NonNull_full_borrow_content(t, l), ptr::NonNull_frac_bc(t, l))(){
            open <ptr::NonNull<T>>.full_borrow_content(t, l)();
            close ptr::NonNull_frac_bc::<T>(t, l)();
        }{
            full_borrow_implies(k, ptr::NonNull_full_borrow_content(t, l), ptr::NonNull_frac_bc(t, l));
            full_borrow_into_frac_m(k, ptr::NonNull_frac_bc(t, l));
        }
    }
    assert [?qf]frac_borrow(k, ptr::NonNull_frac_bc(t, l));
    close [qf]<ptr::NonNull<T>>.share(k, t, l);
}

lem init_ref_ptr::NonNull<T>(p: *ptr::NonNull<T>)
    req type_interp::<T>() &*& atomic_mask(Nlft) &*& ref_init_perm(p, ?x) &*& [_]ptr::NonNull_share::<T>(?k, ?t, x) &*& [?q]lifetime_token(k);
    ens type_interp::<T>() &*& atomic_mask(Nlft) &*& [q]lifetime_token(k) &*& [_]ptr::NonNull_share::<T>(k, t, p) &*& [_]frac_borrow(k, ref_initialized_(p));
{
    assume(false);
}

@*/

pub mod ptr {
    pub struct NonNull<T> {
        pointer: *const T,
    }

    impl<T> NonNull<T> {
        pub fn from(reference: &mut T) -> Self {
            let r = NonNull {
                pointer: reference as *mut T,
            };
            //@ points_to_limits(reference);
            //@ close <ptr::NonNull<T>>.own(_t, r);
            r
        }

        pub unsafe fn new_unchecked(ptr: *mut T) -> Self
            //@ req true;
            //@ ens result.pointer == ptr;
            //@ on_unwind_ens false;
        {
            NonNull { pointer: ptr }
        }

        // TODO: It is a good example to show the unsoundness w.r.t. aliasing semantics of Rust
        pub unsafe fn as_ref<'a>(&'a self) -> &'a T
            //@ req [?q](*self).pointer |-> ?p;
            //@ ens [q](*self).pointer |-> p;
            //@ on_unwind_ens false;
        {
            &*self.pointer
        }

        pub fn as_ptr(self) -> *mut T {
            //@ open <ptr::NonNull<T>>.own(_t, self);
            self.pointer as *mut T
        }
    }

    impl<T> Copy for NonNull<T> {}
    impl<T> Clone for NonNull<T> {
        fn clone<'a>(&'a self) -> Self {
            //@ open ptr::NonNull_share::<T>()('a, _t, self);
            //@ open_frac_borrow('a, ptr::NonNull_frac_bc(_t, self), _q_a);
            //@ open ptr::NonNull_frac_bc::<T>(_t, self)();
            let r = *self;
            //@ open <ptr::NonNull<T>>.own(_t, r);
            //@ assert [?qp](*self).pointer |-> _;
            //@ close [qp]<ptr::NonNull<T>>.own()(_t, r);
            //@ close [qp]ptr::NonNull_frac_bc::<T>(_t, self)();
            //@ close_frac_borrow(qp, ptr::NonNull_frac_bc(_t, self));
            //@ close <ptr::NonNull<T>>.own(_t, r);
            r
        }
    }
}
