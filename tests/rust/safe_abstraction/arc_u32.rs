// verifast_options{ignore_ref_creation}

use std::process::abort;
use std::ptr::NonNull;
use std::sync::atomic::{AtomicUsize, Ordering};

struct ArcInnerU32 {
    strong: AtomicUsize,
    // weak: AtomicUsize,
    data: u32,
}

pub struct ArcU32 {
    ptr: NonNull<ArcInnerU32>,
}

/*@
fix Narc() -> *u8 { 42 as *u8 }
fix Marc() -> mask_t { MaskSingle(Narc) }

pred_ctor dlft_pred(dk: lifetime_t)(gid: isize; destroyed: bool) = ghost_cell(gid, destroyed) &*& if destroyed { true } else { lifetime_token(dk) };

/* While for this concrete Arc type, i.e. ArcU32, we could have the invariant independent of `t: thread_id_t`, since in the corresponding generic example we will get
`borrow_end_token(dk, <T>.full_borrow_content(t, &(*ptr).data))` we kept the invariant close to the generic form.
*/
pred_ctor Arc_inv(dk: lifetime_t, gid: isize, ptr: *ArcInnerU32)() = counting(dlft_pred(dk), gid, ?n, ?destroyed) &*&
    if destroyed { true } else { std::sync::atomic::AtomicUsize(&(*ptr).strong, n) &*& n >= 1 && n <= usize::MAX &*&
    std::alloc::alloc_block(ptr as *u8, std::alloc::Layout::new_::<ArcInnerU32>()) &*& struct_ArcInnerU32_padding(ptr) &*&
    borrow_end_token(dk, u32_full_borrow_content(default_tid, &(*ptr).data)) };

pred <ArcU32>.own(t, arcU32) = [_]std::ptr::NonNull_own(default_tid, arcU32.ptr) &*& [_]exists(?ptr) &*& std::ptr::NonNull_ptr::<ArcInnerU32>(arcU32.ptr) == ptr &*&
    [_]exists(?dk) &*& [_]exists(?gid) &*& [_]atomic_space(Marc, Arc_inv(dk, gid, ptr)) &*& ticket(dlft_pred(dk), gid, ?frac) &*& [frac]dlft_pred(dk)(gid, false) &*&
    [_]u32_share(dk, default_tid, &(*ptr).data) &*& pointer_within_limits(&(*ptr).data) == true;

pred_ctor Arc_frac_bc(l: *ArcU32, nnp: std::ptr::NonNull<ArcInnerU32>)(;) = (*l).ptr |-> nnp;
pred_ctor ticket_(dk: lifetime_t, gid: isize, frac: real)(;) = ticket(dlft_pred(dk), gid, frac) &*& [frac]ghost_cell(gid, false);

pred <ArcU32>.share(k, t, l) = [_]exists(?nnp) &*& [_]frac_borrow(k, Arc_frac_bc(l, nnp)) &*& [_]std::ptr::NonNull_own(default_tid, nnp) &*&
    [_]exists(?ptr) &*& std::ptr::NonNull_ptr::<ArcInnerU32>(nnp) == ptr &*& [_]exists(?dk) &*& [_]exists(?gid) &*& [_]atomic_space(Marc, Arc_inv(dk, gid, ptr)) &*&
    [_]exists(?frac) &*& [_]frac_borrow(k, ticket_(dk, gid, frac)) &*& [_]frac_borrow(k, lifetime_token_(frac, dk)) &*& [_]u32_share(dk, default_tid, &(*ptr).data) &*&
    pointer_within_limits(&(*ptr).data) == true;

lem ArcU32_share_mono(k: lifetime_t, k1: lifetime_t, t: thread_id_t, l: *ArcU32)
    req lifetime_inclusion(k1, k) == true &*& [_]ArcU32_share(k, t, l);
    ens [_]ArcU32_share(k1, t, l);
{
    open ArcU32_share(k, t, l);
    assert [_]exists::<std::ptr::NonNull<ArcInnerU32>>(?nnp) &*& [_]exists::<lifetime_t>(?dk) &*& [_]exists::<isize>(?gid) &*& [_]exists::<real>(?frac);
    frac_borrow_mono(k, k1, Arc_frac_bc(l, nnp));
    frac_borrow_mono(k, k1, ticket_(dk, gid, frac));
    frac_borrow_mono(k, k1, lifetime_token_(frac, dk));
    close ArcU32_share(k1, t, l);
    leak ArcU32_share(k1, _, _);
}

pred_ctor Ctx(nnp: std::ptr::NonNull<ArcInnerU32>, dk: lifetime_t, gid: isize, l: *ArcU32)() = [_]std::ptr::NonNull_own(default_tid, nnp) &*&
    [_]exists(?ptr) &*& std::ptr::NonNull_ptr::<ArcInnerU32>(nnp) == ptr &*& [_]exists(dk) &*& [_]exists(gid) &*& [_]atomic_space(Marc, Arc_inv(dk, gid, ptr)) &*&
    [_]u32_share(dk, default_tid, &(*ptr).data) &*& struct_ArcU32_padding(l);

lem ArcU32_fbor_split(k: lifetime_t, t: thread_id_t, l: *ArcU32)
    req atomic_mask(Nlft) &*& [?qk]lifetime_token(k) &*& full_borrow(k, ArcU32_full_borrow_content(t, l));
    ens atomic_mask(Nlft) &*& [qk]lifetime_token(k) &*&
        [_]exists(?nnp) &*& full_borrow(k, Arc_frac_bc(l, nnp)) &*& [_]std::ptr::NonNull_own(default_tid, nnp) &*&
        [_]exists(?ptr) &*& std::ptr::NonNull_ptr::<ArcInnerU32>(nnp) == ptr &*& [_]exists(?dk) &*& [_]exists(?gid) &*& [_]atomic_space(Marc, Arc_inv(dk, gid, ptr)) &*&
        [_]exists(?frac) &*& full_borrow(k, ticket_(dk, gid, frac)) &*& full_borrow(k, lifetime_token_(frac, dk)) &*& [_]u32_share(dk, default_tid, &(*ptr).data) &*&
        pointer_within_limits(&(*ptr).data) == true;
{
    let klong = open_full_borrow_strong_m(k, ArcU32_full_borrow_content(t, l), qk);
    open ArcU32_full_borrow_content(t, l)();
    open ArcU32_own(t, ?arcU32);
    let nnp = arcU32.ptr;
    assert [_]exists::<lifetime_t>(?dk) &*& ticket(_, ?gid, ?frac);
    close Arc_frac_bc(l, nnp)();
    close sep(ticket_(dk, gid, frac), lifetime_token_(frac, dk))();
    close sep(Arc_frac_bc(l, nnp), sep(ticket_(dk, gid, frac), lifetime_token_(frac, dk)))();
    produce_lem_ptr_chunk full_borrow_convert_strong( Ctx(nnp, dk, gid, l), sep(Arc_frac_bc(l, nnp), sep(ticket_(dk, gid, frac), lifetime_token_(frac, dk))), klong,
        ArcU32_full_borrow_content(t, l))() {
            open sep(Arc_frac_bc(l, nnp), sep(ticket_(dk, gid, frac), lifetime_token_(frac, dk)))();
            open Arc_frac_bc(l, nnp)();
            open sep(ticket_(dk, gid, frac), lifetime_token_(frac, dk))();
            open ticket_(dk, gid, frac)();
            open Ctx(nnp, dk, gid, l)();
            close ArcU32_own(t, arcU32);
            close ArcU32_full_borrow_content(t, l)();
        }{
            close Ctx(nnp, dk, gid, l)();
            close_full_borrow_strong_m(klong, ArcU32_full_borrow_content(t, l), sep(Arc_frac_bc(l, nnp), sep(ticket_(dk, gid, frac), lifetime_token_(frac, dk))));
        }
        full_borrow_mono(klong, k, sep(Arc_frac_bc(l, nnp), sep(ticket_(dk, gid, frac), lifetime_token_(frac, dk))));
        full_borrow_split_m(k, Arc_frac_bc(l, nnp), sep(ticket_(dk, gid, frac), lifetime_token_(frac, dk)));
        full_borrow_split_m(k, ticket_(dk, gid, frac), lifetime_token_(frac, dk));
        leak exists(nnp);
        leak exists(frac);
}

lem ArcU32_share_full(k: lifetime_t, t: thread_id_t, l: *ArcU32)
    req atomic_mask(Nlft) &*& [?q]lifetime_token(k) &*& full_borrow(k, ArcU32_full_borrow_content(t, l));
    ens atomic_mask(Nlft) &*& [q]lifetime_token(k) &*& [_]ArcU32_share(k, t, l);
{
    ArcU32_fbor_split(k, t, l);
    assert [_]exists::<std::ptr::NonNull<ArcInnerU32>>(?nnp) &*& [_]exists::<lifetime_t>(?dk) &*& [_]exists::<isize>(?gid) &*& [_]exists::<real>(?frac);
    full_borrow_into_frac_m(k, Arc_frac_bc(l, nnp));
    full_borrow_into_frac_m(k, ticket_(dk, gid, frac));
    full_borrow_into_frac_m(k, lifetime_token_(frac, dk));
    close ArcU32_share(k, t, l);
    leak ArcU32_share(k, t, l);
}

lem init_ref_ArcU32(p: *ArcU32)
    req atomic_mask(Nlft) &*& ref_init_perm(p, ?x) &*& [_]ArcU32_share(?k, ?t, x) &*& [?q]lifetime_token(k);
    ens atomic_mask(Nlft) &*& [q]lifetime_token(k) &*& [_]ArcU32_share(k, t, p) &*& [_]frac_borrow(k, ref_initialized_(p));
{
    assume(false);
}

@*/

unsafe impl Send for ArcU32 {}
unsafe impl Sync for ArcU32 {}

impl ArcU32 {
    pub fn new(data: u32) -> ArcU32 {
        unsafe {
            let l = std::alloc::Layout::new::<ArcInnerU32>();
            let p = std::alloc::alloc(l) as *mut ArcInnerU32;
            if p.is_null() {
                std::alloc::handle_alloc_error(l);
            }
            //@ close_struct(p);
            std::ptr::write(p, ArcInnerU32 {
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
            //@ close u32_full_borrow_content(default_tid, &(*p).data)();
            //@ borrow(dk, u32_full_borrow_content(default_tid, &(*p).data));
            //@ close Arc_inv(dk, gid, p)();
            //@ create_atomic_space(Marc, Arc_inv(dk, gid, p));
            //@ leak atomic_space(Marc, Arc_inv(dk, gid, p));
            //@ full_borrow_into_frac(dk, u32_full_borrow_content(default_tid, &(*p).data));
            //@ close u32_share(dk, default_tid, &(*p).data);
            //@ leak u32_share(_, _, _);
            //@ leak exists(p);
            //@ leak exists(dk);
            //@ leak exists::<isize>(gid);
            //@ std::ptr::close_NonNull_own::<ArcInnerU32>(default_tid, nnp);
            //@ leak std::ptr::NonNull_own::<ArcInnerU32>()(default_tid, nnp);
            //@ close ArcU32_own(_t, ret);
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

    unsafe fn strong_count_inner<'a>(ptr: &'a ArcInnerU32) -> usize
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
                open Arc_inv(dk, gid, ptr)();
                Arc_is_not_destroyed(dk, frac);
                assert std::sync::atomic::is_AtomicUsize_load_op(?op, _, _, ?Q);
                op();
                close Arc_inv(dk, gid, ptr)();
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
            //@ open ArcU32_share('a, _t, this);
            //@ assert [_]exists::<std::ptr::NonNull<ArcInnerU32>>(?nnp);
            //@ open_frac_borrow('a, Arc_frac_bc(this, nnp), _q_a/2);
            //@ open [?qnnp]Arc_frac_bc(this, nnp)();
            let ret = Self::strong_count_inner(this.ptr.as_ref());
            //@ close [qnnp]Arc_frac_bc(this, nnp)();
            //@ close_frac_borrow(qnnp, Arc_frac_bc(this, nnp));
            ret
        }
    }

    unsafe fn clone_inner<'a>(ptr: &'a ArcInnerU32)
    /*@ req [?qa]lifetime_token(?a) &*& [_]exists(?dk) &*& [_]exists(?gid) &*& [_]atomic_space(Marc, Arc_inv(dk, gid, ptr)) &*&
        [_]exists(?frac) &*& [_]frac_borrow(a, ticket_(dk, gid, frac)) &*& [_]frac_borrow(a, lifetime_token_(frac, dk)); @*/
    //@ ens [qa]lifetime_token(a) &*& ticket(dlft_pred(dk), gid, ?frac1) &*& [frac1]dlft_pred(dk)(gid, false);
    {
        let current = Self::strong_count_inner(ptr);
        if current >= usize::MAX { abort(); }
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
            open Arc_inv(dk, gid, ptr)();
            Arc_is_not_destroyed(dk, frac);
            assert std::sync::atomic::is_AtomicUsize_compare_exchange_op(?op, _, _, _, _, ?Q);
            op();
            assert Q(?result);
            if result == std::result::Result::Ok(current) {
                create_ticket(dlft_pred(dk), gid);
            } else {}
            close Arc_inv(dk, gid, ptr)();
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

impl std::ops::Deref for ArcU32 {
    type Target = u32;

    fn deref<'a>(&'a self) -> &'a u32 {
        unsafe {
            //@ open ArcU32_share('a, _t, self);
            //@ assert [_]exists::<std::ptr::NonNull<ArcInnerU32>>(?nnp) &*& [_]exists::<real>(?frac) &*& [_]exists::<lifetime_t>(?dk);
            //@ open_frac_borrow('a, Arc_frac_bc(self, nnp), _q_a);
            //@ open [?qnnp]Arc_frac_bc(self, nnp)();
            let ret = &self.ptr.as_ref().data;
            //@ close [qnnp]Arc_frac_bc(self, nnp)();
            //@ close_frac_borrow(qnnp, Arc_frac_bc(self, nnp));
            //@ frac_borrow_lft_incl('a, frac, dk);
            //@ u32_share_mono(dk, 'a, default_tid, ret);
            //@ u32_sync('a, default_tid, _t, ret);
            //@ open u32_share('a, _t, _);
            ret
        }
    }
}

impl Clone for ArcU32 {
    fn clone<'a>(&'a self) -> ArcU32 {
        //@ open ArcU32_share('a, _t, self);
        //@ assert [_]exists::<std::ptr::NonNull<ArcInnerU32>>(?nnp);
        //@ open_frac_borrow('a, Arc_frac_bc(self, nnp), _q_a/2);
        //@ open [?qnnp]Arc_frac_bc(self, nnp)();
        unsafe { Self::clone_inner(self.ptr.as_ref()) };
        let ret = Self { ptr: self.ptr };
        //@ close [qnnp]Arc_frac_bc(self, nnp)();
        //@ close_frac_borrow(qnnp, Arc_frac_bc(self, nnp));
        //@ close ArcU32_own(_t, ret);
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

impl Drop for ArcU32 {
    fn drop<'a>(&'a mut self) {
        //@ open ArcU32_full_borrow_content(_t, self)();
        //@ open ArcU32_own(_t, ?arcU32);
        //@ assert [_]exists::<lifetime_t>(?dk) &*& [_]exists::<isize>(?gid) &*& [_]exists::<*ArcInnerU32>(?ptr);
        //@ let sp = &(*ptr).strong;
        unsafe {
            {
            /*@
            pred Pre() = [_]atomic_space(Marc, Arc_inv(dk, gid, ptr)) &*& ticket(dlft_pred(dk), gid, ?frac) &*& [frac]dlft_pred(dk)(gid, false);
            pred Post(result: usize) = if result == 1 {
                    *sp |-> ?_x0 &*& (*ptr).data |-> ?_x1 &*& struct_ArcInnerU32_padding(ptr) &*& std::alloc::alloc_block(ptr as *u8, std::alloc::Layout::new_::<ArcInnerU32>())
                } else { true };
            @*/
            /*@
            produce_lem_ptr_chunk std::sync::atomic::AtomicUsize_fetch_sub_ghop(sp, 1, Pre, Post)() {
                open Pre();
                open_atomic_space(Marc, Arc_inv(dk, gid, ptr));
                open Arc_inv(dk, gid, ptr)();
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
                    borrow_end_m(dk, u32_full_borrow_content(default_tid, &(*ptr).data));
                    open u32_full_borrow_content(default_tid, &(*ptr).data)();
                } else {}
                close Arc_inv(dk, gid, ptr)();
                close_atomic_space(Marc);
                close Post(v0);
            };
            @*/
            //@ close Pre();
            let sco = self.ptr.as_ref().strong.fetch_sub(1, Ordering::SeqCst);
            //@ open Post(sco);
            //@ std::ptr::open_NonNull_own::<ArcInnerU32>(default_tid, arcU32.ptr);
            //@ std::ptr::close_NonNull_own::<ArcInnerU32>(_t, arcU32.ptr);
            if sco != 1 { return; }
            }
            //@ open_struct(ptr);
            std::alloc::dealloc(self.ptr.as_ptr() as *mut u8, std::alloc::Layout::new::<ArcInnerU32>());
        }
    }
}
