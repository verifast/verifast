use std::process::abort;
use std::ptr::NonNull;
use std::sync::atomic::{AtomicUsize, Ordering};

struct ArcInner<T> {
    strong: AtomicUsize,
    // weak: AtomicUsize,
    data: T,
}

pub struct Arc<T: Sync + Send> {
    ptr: NonNull<ArcInner<T>>,
}

/*@

fix Narc() -> *u8 { 42 as *u8 }
fix Marc() -> mask_t { MaskSingle(Narc) }

pred_ctor dlft_pred(dk: lifetime_t)(gid: isize; destroyed: bool) = ghost_cell(gid, destroyed) &*& if destroyed { true } else { lifetime_token(dk) };

pred_ctor Arc_inv<T>(dk: lifetime_t, gid: isize, ptr: *ArcInner<T>)() = counting(dlft_pred(dk), gid, ?n, ?destroyed) &*&
    if destroyed { true } else { std::sync::atomic::AtomicUsize(&(*ptr).strong, n) &*& n >= 1 && n <= usize::MAX &*&
    std::alloc::alloc_block(ptr as *u8, std::alloc::Layout::new_::<ArcInner<T>>()) &*& struct_ArcInner_padding::<T>(ptr) &*&
    borrow_end_token(dk, <T>.full_borrow_content(default_tid, &(*ptr).data)) };

pred<T> <Arc<T>>.own(t, arc) = [_]std::ptr::NonNull_own(default_tid, arc.ptr) &*& [_]exists(?ptr) &*& std::ptr::NonNull_ptr::<ArcInner<T>>(arc.ptr) == ptr &*&
    [_]exists(?dk) &*& [_]exists(?gid) &*& [_]atomic_space(Marc, Arc_inv(dk, gid, ptr)) &*& ticket(dlft_pred(dk), gid, ?frac) &*& [frac]dlft_pred(dk)(gid, false) &*&
    [_](<T>.share)(dk, default_tid, &(*ptr).data) &*& pointer_within_limits(&(*ptr).data) == true &*& is_Send(typeid(T)) == true;

pred_ctor Arc_frac_bc<T>(l: *Arc<T>, nnp: std::ptr::NonNull<ArcInner<T>>)(;) = (*l).ptr |-> nnp;
pred_ctor ticket_(dk: lifetime_t, gid: isize, frac: real)(;) = ticket(dlft_pred(dk), gid, frac) &*& [frac]ghost_cell(gid, false);

pred<T> <Arc<T>>.share(k, t, l) = [_]exists(?nnp) &*& [_]frac_borrow(k, Arc_frac_bc(l, nnp)) &*& [_]std::ptr::NonNull_own(default_tid, nnp) &*&
    [_]exists(?ptr) &*& std::ptr::NonNull_ptr::<ArcInner<T>>(nnp) == ptr &*& [_]exists(?dk) &*& [_]exists(?gid) &*& [_]atomic_space(Marc, Arc_inv(dk, gid, ptr)) &*&
    [_]exists(?frac) &*& [_]frac_borrow(k, ticket_(dk, gid, frac)) &*& [_]frac_borrow(k, lifetime_token_(frac, dk)) &*& [_](<T>.share)(dk, default_tid, &(*ptr).data) &*&
    pointer_within_limits(&(*ptr).data) == true;

lem Arc_share_mono<T>(k: lifetime_t, k1: lifetime_t, t: thread_id_t, l: *Arc<T>)
    req lifetime_inclusion(k1, k) == true &*& [_]Arc_share(k, t, l);
    ens [_]Arc_share(k1, t, l);
{
    open Arc_share::<T>()(k, t, l);
    assert [_]exists::<std::ptr::NonNull<ArcInner<T>>>(?nnp) &*& [_]exists::<lifetime_t>(?dk) &*& [_]exists::<isize>(?gid) &*& [_]exists::<real>(?frac);
    frac_borrow_mono(k, k1, Arc_frac_bc(l, nnp));
    frac_borrow_mono(k, k1, ticket_(dk, gid, frac));
    frac_borrow_mono(k, k1, lifetime_token_(frac, dk));
    close Arc_share::<T>()(k1, t, l);
    leak Arc_share::<T>()(k1, _, _);
}

pred_ctor Ctx<T>(nnp: std::ptr::NonNull<ArcInner<T>>, dk: lifetime_t, gid: isize, l: *Arc<T>)() = [_]std::ptr::NonNull_own(default_tid, nnp) &*&
    [_]exists(?ptr) &*& std::ptr::NonNull_ptr::<ArcInner<T>>(nnp) == ptr &*& [_]exists(dk) &*& [_]exists(gid) &*& [_]atomic_space(Marc, Arc_inv(dk, gid, ptr)) &*&
    [_](<T>.share)(dk, default_tid, &(*ptr).data) &*& struct_Arc_padding(l);

lem Arc_fbor_split<T>(k: lifetime_t, t: thread_id_t, l: *Arc<T>)
    req atomic_mask(Nlft) &*& [?qk]lifetime_token(k) &*& full_borrow(k, Arc_full_borrow_content(t, l));
    ens atomic_mask(Nlft) &*& [qk]lifetime_token(k) &*&
        [_]exists(?nnp) &*& full_borrow(k, Arc_frac_bc(l, nnp)) &*& [_]std::ptr::NonNull_own(default_tid, nnp) &*&
        [_]exists(?ptr) &*& std::ptr::NonNull_ptr::<ArcInner<T>>(nnp) == ptr &*& [_]exists(?dk) &*& [_]exists(?gid) &*& [_]atomic_space(Marc, Arc_inv(dk, gid, ptr)) &*&
        [_]exists(?frac) &*& full_borrow(k, ticket_(dk, gid, frac)) &*& full_borrow(k, lifetime_token_(frac, dk)) &*& [_](<T>.share)(dk, default_tid, &(*ptr).data) &*&
        pointer_within_limits(&(*ptr).data) == true;
{
    let klong = open_full_borrow_strong_m(k, Arc_full_borrow_content(t, l), qk);
    open Arc_full_borrow_content::<T>(t, l)();
    open Arc_own::<T>()(t, ?arc);
    let nnp = arc.ptr;
    assert [_]exists::<lifetime_t>(?dk) &*& ticket(_, ?gid, ?frac);
    close Arc_frac_bc::<T>(l, nnp)();
    close sep(ticket_(dk, gid, frac), lifetime_token_(frac, dk))();
    close sep(Arc_frac_bc(l, nnp), sep(ticket_(dk, gid, frac), lifetime_token_(frac, dk)))();
    produce_lem_ptr_chunk full_borrow_convert_strong( Ctx(nnp, dk, gid, l), sep(Arc_frac_bc(l, nnp), sep(ticket_(dk, gid, frac), lifetime_token_(frac, dk))), klong,
        Arc_full_borrow_content(t, l))() {
            open sep(Arc_frac_bc(l, nnp), sep(ticket_(dk, gid, frac), lifetime_token_(frac, dk)))();
            open Arc_frac_bc::<T>(l, nnp)();
            open sep(ticket_(dk, gid, frac), lifetime_token_(frac, dk))();
            open ticket_(dk, gid, frac)();
            open Ctx::<T>(nnp, dk, gid, l)();
            close Arc_own::<T>()(t, arc);
            close Arc_full_borrow_content::<T>(t, l)();
        }{
            close Ctx::<T>(nnp, dk, gid, l)();
            close_full_borrow_strong_m(klong, Arc_full_borrow_content(t, l), sep(Arc_frac_bc(l, nnp), sep(ticket_(dk, gid, frac), lifetime_token_(frac, dk))));
        }
        full_borrow_mono(klong, k, sep(Arc_frac_bc(l, nnp), sep(ticket_(dk, gid, frac), lifetime_token_(frac, dk))));
        full_borrow_split_m(k, Arc_frac_bc(l, nnp), sep(ticket_(dk, gid, frac), lifetime_token_(frac, dk)));
        full_borrow_split_m(k, ticket_(dk, gid, frac), lifetime_token_(frac, dk));
        leak exists(nnp);
        leak exists(frac);
}

lem Arc_share_full<T>(k: lifetime_t, t: thread_id_t, l: *Arc<T>)
    req atomic_mask(Nlft) &*& [?q]lifetime_token(k) &*& full_borrow(k, Arc_full_borrow_content(t, l));
    ens atomic_mask(Nlft) &*& [q]lifetime_token(k) &*& [_]Arc_share(k, t, l);
{
    Arc_fbor_split(k, t, l);
    assert [_]exists::<std::ptr::NonNull<ArcInner<T>>>(?nnp) &*& [_]exists::<lifetime_t>(?dk) &*& [_]exists::<isize>(?gid) &*& [_]exists::<real>(?frac);
    full_borrow_into_frac_m(k, Arc_frac_bc(l, nnp));
    full_borrow_into_frac_m(k, ticket_(dk, gid, frac));
    full_borrow_into_frac_m(k, lifetime_token_(frac, dk));
    close Arc_share::<T>()(k, t, l);
    leak Arc_share(k, t, l);
}

@*/

unsafe impl<T: Sync + Send> Send for Arc<T> {}
unsafe impl<T: Sync + Send> Sync for Arc<T> {}

impl<T: Sync + Send> Arc<T> {
    pub fn new(data: T) -> Arc<T> {
        unsafe {
            let l = std::alloc::Layout::new::<ArcInner<T>>();
            //@ std::alloc::Layout_size__Layout_from_size_align_(std::mem::size_of_::<ArcInner<T>>(), std::mem::align_of_::<ArcInner<T>>());
            let p = std::alloc::alloc(l) as *mut ArcInner<T>;
            if p.is_null() {
                std::alloc::handle_alloc_error(l);
            }
            //@ close_struct(p);
            std::ptr::write(p, ArcInner {
                strong: AtomicUsize::new(1),
                data,
            });
            let ret = Self {
                ptr: NonNull::new_unchecked(p),
            };
            //@ let nnp = ret.ptr;
            //@ let dk = begin_lifetime();
            //@ let gid = create_ghost_cell(false); //destroyed
            //@ close dlft_pred(dk)(gid, false);
            //@ start_counting(dlft_pred(dk), gid);
            //@ let frac = create_ticket(dlft_pred(dk), gid);
            //@ close std::sync::atomic::AtomicUsize(&(*p).strong, 1);
            //@ open ArcInner_data(p, ?v);
            //@ assert thread_token(?t);
            //@ produce_type_interp::<T>();
            //@ Send::send::<T>(t, default_tid, v);
            //@ leak type_interp::<T>();
            //@ close_full_borrow_content::<T>(default_tid, &(*p).data);
            //@ borrow(dk, <T>.full_borrow_content(default_tid, &(*p).data));
            //@ close Arc_inv::<T>(dk, gid, p)();
            //@ create_atomic_space(Marc, Arc_inv(dk, gid, p));
            //@ leak atomic_space(Marc, Arc_inv(dk, gid, p));
            //@ share_full_borrow::<T>(dk, default_tid, &(*p).data);
            //@ leak exists(p);
            //@ leak exists(dk);
            //@ leak exists::<isize>(gid);
            //@ close std::ptr::NonNull_own::<ArcInner<T>>()(default_tid, nnp);
            //@ leak std::ptr::NonNull_own::<ArcInner<T>>()(default_tid, nnp);
            //@ close Arc_own::<T>()(_t, ret);
            ret
        }
    }

    /*@
    
    lem close_dlft_pred() -> real
        req [?q]ghost_cell(?gid, false) &*& [?q1]lifetime_token(?dk);
        ens [result]dlft_pred(dk)(gid, false) &*& [q - result]ghost_cell(gid, false) &*& [q1 - result]lifetime_token(dk);
    {
        lifetime_token_inv(dk);
        ghost_cell_fraction_info(gid);
        return if q < q1 { q/2 } else { q1/2 };
    }

    lem Arc_is_not_destroyed(dk: lifetime_t, frac: real)
        req atomic_mask(?mask) &*& mask_le(Nlft, mask) == true &*& counting(dlft_pred(dk), ?gid, ?n, ?destroyed) &*&
            [_]frac_borrow(?k, ticket_(dk, gid, frac)) &*& [_]frac_borrow(k, lifetime_token_(frac, dk)) &*& [?q]lifetime_token(k);
        ens atomic_mask(mask) &*& counting(dlft_pred(dk), gid, n, destroyed) &*& [q]lifetime_token(k) &*& destroyed == false;
    {
        open_frac_borrow_m(k, ticket_(dk, gid, frac), q/2);
        open_frac_borrow_m(k, lifetime_token_(frac, dk), q/2);
        open [?qt]ticket_(dk, gid, frac)();
        open [?qdk]lifetime_token_(frac, dk)();
        let qp = close_dlft_pred();
        counting_match_fraction(dlft_pred(dk), gid);
        open dlft_pred(dk)(gid, false);
        close [qdk]lifetime_token_(frac, dk)();
        close [qt]ticket_(dk, gid, frac)();
        close_frac_borrow_m(qdk, lifetime_token_(frac, dk));
        close_frac_borrow_m(qt, ticket_(dk, gid, frac));
    }
    
    @*/

    unsafe fn strong_count_inner<'a>(ptr: &'a ArcInner<T>) -> usize
    /*@ req [?qa]lifetime_token(?a) &*& [_]exists(?dk) &*& [_]exists(?gid) &*& [_]atomic_space(Marc, Arc_inv(dk, gid, ptr)) &*&
        [_]exists(?frac) &*& [_]frac_borrow(a, ticket_(dk, gid, frac)) &*& [_]frac_borrow(a, lifetime_token_(frac, dk));
    @*/
    //@ ens [qa]lifetime_token(a);
    {
        let ret;
        {
            /*@
            pred Pre() = [qa]lifetime_token(a) &*& [_]atomic_space(Marc, Arc_inv(dk, gid, ptr)) &*&
                [_]frac_borrow(a, ticket_(dk, gid, frac)) &*& [_]frac_borrow(a, lifetime_token_(frac, dk));
            pred Post(r: usize;) = [qa]lifetime_token(a);
            @*/
            /*@
            produce_lem_ptr_chunk std::sync::atomic::AtomicUsize_load_ghop(&(*ptr).strong, Pre, Post)() {
                open Pre();
                open_atomic_space(Marc, Arc_inv(dk, gid, ptr));
                open Arc_inv::<T>(dk, gid, ptr)();
                Arc_is_not_destroyed(dk, frac);
                assert std::sync::atomic::is_AtomicUsize_load_op(?op, _, _, ?Q);
                op();
                close Arc_inv::<T>(dk, gid, ptr)();
                close_atomic_space(Marc);
                assert Q(?r);
                close Post(r);
            };
            @*/
            //@ close Pre();
            ret = ptr.strong.load(Ordering::SeqCst);
            //@ open Post(ret);
        }
        return ret;
    }

    pub fn strong_count<'a>(this: &'a Self) -> usize {
        unsafe {
            //@ open Arc_share::<T>()('a, _t, this);
            //@ assert [_]exists::<std::ptr::NonNull<ArcInner<T>>>(?nnp);
            //@ open_frac_borrow('a, Arc_frac_bc(this, nnp), _q_a/2);
            //@ open [?qnnp]Arc_frac_bc::<T>(this, nnp)();
            let ret = Self::strong_count_inner(this.ptr.as_ref());
            //@ close [qnnp]Arc_frac_bc::<T>(this, nnp)();
            //@ close_frac_borrow(qnnp, Arc_frac_bc(this, nnp));
            ret
        }
    }

    unsafe fn clone_inner<'a>(ptr: &'a ArcInner<T>)
    /*@ req [?qa]lifetime_token(?a) &*& [_]exists(?dk) &*& [_]exists(?gid) &*& [_]atomic_space(Marc, Arc_inv(dk, gid, ptr)) &*&
        [_]exists(?frac) &*& [_]frac_borrow(a, ticket_(dk, gid, frac)) &*& [_]frac_borrow(a, lifetime_token_(frac, dk)); @*/
    //@ ens [qa]lifetime_token(a) &*& ticket(dlft_pred(dk), gid, ?frac1) &*& [frac1]dlft_pred(dk)(gid, false);
    {
        let current = Self::strong_count_inner(ptr);
        if current >= 0xFFFF { abort(); } //TODO: Use `usize::MAX` instead of `0xFFFF`
        let cas_res;
        {
        /*@
        pred Pre() = [qa]lifetime_token(a) &*& [_]atomic_space(Marc, Arc_inv(dk, gid, ptr)) &*&
            [_]frac_borrow(a, ticket_(dk, gid, frac)) &*& [_]frac_borrow(a, lifetime_token_(frac, dk));
        pred Post(result: std::result::Result<usize, usize>) = [qa]lifetime_token(a) &*&
            match result {
                Result::Ok(_current) => ticket(dlft_pred(dk), gid, ?frac1) &*& [frac1]dlft_pred(dk)(gid, false),
                Result::Err(_current) => true,
            };
        @*/
        /*@
        produce_lem_ptr_chunk std::sync::atomic::AtomicUsize_compare_exchange_ghop(&(*ptr).strong, current, current + 1, Pre, Post)() {
            open Pre();
            open_atomic_space(Marc, Arc_inv(dk, gid, ptr));
            open Arc_inv::<T>(dk, gid, ptr)();
            Arc_is_not_destroyed(dk, frac);
            assert std::sync::atomic::is_AtomicUsize_compare_exchange_op(?op, _, _, _, _, ?Q);
            op();
            assert Q(?result);
            if result == std::result::Result::Ok(current) {
                create_ticket(dlft_pred(dk), gid);
            } else {}
            close Arc_inv::<T>(dk, gid, ptr)();
            close_atomic_space(Marc);
            close Post(result);
        };
        @*/
        //@ close Pre();
        cas_res = ptr.strong.compare_exchange(current, current + 1, Ordering::SeqCst, Ordering::SeqCst);
        //@ open Post(cas_res);
        }
        match cas_res {
            Ok(_) => return, //TODO: change `return` to `()`. It needs tuple aggregate encoding
            Err(_) => Self::clone_inner(ptr),
        }
    }
}

impl<T: Sync + Send> std::ops::Deref for Arc<T> {
    type Target = T;

    fn deref<'a>(&'a self) -> &'a T {
        unsafe {
            //@ open Arc_share::<T>()('a, _t, self);
            //@ assert [_]exists::<std::ptr::NonNull<ArcInner<T>>>(?nnp) &*& [_]exists::<real>(?frac) &*& [_]exists::<lifetime_t>(?dk);
            //@ open_frac_borrow('a, Arc_frac_bc(self, nnp), _q_a);
            //@ open [?qnnp]Arc_frac_bc::<T>(self, nnp)();
            let ret = &self.ptr.as_ref().data;
            //@ close [qnnp]Arc_frac_bc::<T>(self, nnp)();
            //@ close_frac_borrow(qnnp, Arc_frac_bc(self, nnp));
            //@ frac_borrow_lft_incl('a, frac, dk);
            //@ produce_type_interp::<T>();
            //@ share_mono::<T>(dk, 'a, default_tid, ret);
            //@ Sync::sync::<T>('a, default_tid, _t, ret);
            //@ leak type_interp::<T>();
            ret
        }
    }
}

impl<T: Sync + Send> Clone for Arc<T> {
    fn clone<'a>(&'a self) -> Arc<T> {
        //@ open Arc_share::<T>()('a, _t, self);
        //@ assert [_]exists::<std::ptr::NonNull<ArcInner<T>>>(?nnp);
        //@ open_frac_borrow('a, Arc_frac_bc(self, nnp), _q_a/2);
        //@ open [?qnnp]Arc_frac_bc::<T>(self, nnp)();
        unsafe { Self::clone_inner(self.ptr.as_ref()) };
        let ret = Self { ptr: self.ptr };
        //@ close [qnnp]Arc_frac_bc::<T>(self, nnp)();
        //@ close_frac_borrow(qnnp, Arc_frac_bc(self, nnp));
        //@ close Arc_own::<T>()(_t, ret);
        ret
    }
}

/*@

lem mod_eq_minus_one(x: i32, m: i32)
    req 1 <= x &*& x <= m;
    ens (x + m) % (m + 1) == x - 1;
{
    div_rem_nonneg(x + m, m + 1);
    assert x + m == (x + m) / (m + 1) * (m + 1) + (x + m) % (m + 1);
    if ((x + m) / (m + 1) < 1) {} else {
        if ((x + m) / (m + 1) > 1) {
            assert 2 <= (x + m) / (m + 1);
            mul_mono_l(2, (x + m) / (m + 1), m + 1);
        } else {}
    }
    assert (x + m) / (m + 1) == 1;
}

@*/

impl<T: Sync + Send> Drop for Arc<T> {
    fn drop<'a>(&'a mut self) {
        //@ open Arc_full_borrow_content::<T>(_t, self)();
        //@ open Arc_own::<T>(_t, ?arc);
        //@ assert [_]exists::<lifetime_t>(?dk) &*& [_]exists::<isize>(?gid) &*& [_]exists::<*ArcInner<T>>(?ptr);
        //@ let sp = &(*ptr).strong;
        unsafe {
            {
            /*@
            pred Pre() = [_]atomic_space(Marc, Arc_inv(dk, gid, ptr)) &*& ticket(dlft_pred(dk), gid, ?frac) &*& [frac]dlft_pred(dk)(gid, false);
            pred Post(result: usize) = if result == 1 {
                    *sp |-> ?_x0 &*& (*ptr).data |-> ?_x1 &*& <T>.own(default_tid, _x1) &*& struct_ArcInner_padding::<T>(ptr) &*& std::alloc::alloc_block(ptr as *u8, std::alloc::Layout::new_::<ArcInner<T>>())
                } else { true };
            @*/
            /*@
            produce_lem_ptr_chunk std::sync::atomic::AtomicUsize_fetch_sub_ghop(sp, 1, Pre, Post)() {
                open Pre();
                open_atomic_space(Marc, Arc_inv(dk, gid, ptr));
                open Arc_inv::<T>(dk, gid, ptr)();
                counting_match_fraction(dlft_pred(dk), gid);
                assert std::sync::atomic::is_AtomicUsize_fetch_sub_op(?op, _, _, _, ?Q);
                op();
                assert Q(?v0);
                destroy_ticket(dlft_pred(dk), gid);
                mod_eq_minus_one(v0, usize::MAX);
                if v0 == 1 {
                    stop_counting(dlft_pred(dk), gid);
                    open dlft_pred(dk)(gid, false);
                    ghost_cell_mutate(gid, true);
                    close dlft_pred(dk)(gid, true);
                    start_counting(dlft_pred(dk), gid);
                    open std::sync::atomic::AtomicUsize(sp, 0);
                    end_lifetime_m(dk);
                    borrow_end_m(dk, <T>.full_borrow_content(default_tid, &(*ptr).data));
                    open_full_borrow_content::<T>(default_tid, &(*ptr).data);
                    close ArcInner_data(ptr, ?v);
                } else {}
                close Arc_inv::<T>(dk, gid, ptr)();
                close_atomic_space(Marc);
                close Post(v0);
            };
            @*/
            //@ close Pre();
            let sco = self.ptr.as_ref().strong.fetch_sub(1, Ordering::SeqCst);
            //@ open Post(sco);
            //@ open std::ptr::NonNull_own::<ArcInner<T>>(default_tid, arc.ptr);
            //@ close std::ptr::NonNull_own::<ArcInner<T>>()(_t, arc.ptr);
            if sco != 1 { return; }
            }
            //@ assert (*ptr).data |-> ?v;
            //@ produce_type_interp::<T>();
            //@ Send::send::<T>(default_tid, _t, v);
            //@ leak type_interp::<T>();
            //@ open ArcInner_data(ptr, v);
            //@ close_full_borrow_content::<T>(_t, &(*ptr).data);
            std::ptr::drop_in_place(&mut (*self.ptr.as_ptr()).data);
            //@ open_struct(ptr);
            //@ std::alloc::Layout_size__Layout_from_size_align_(std::mem::size_of::<ArcInner<T>>(), std::mem::align_of_::<ArcInner<T>>());
            std::alloc::dealloc(self.ptr.as_ptr() as *mut u8, std::alloc::Layout::new::<ArcInner<T>>());
        }
    }
}
