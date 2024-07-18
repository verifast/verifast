use std::process::abort;
use std::ptr::NonNull;
use std::sync::atomic::{AtomicUsize, Ordering};

const MAX_REFCOUNT: usize = (isize::MAX) as usize;

pub struct ArcU32 {
    ptr: NonNull<ArcInnerU32>,
}

/*@
fix Narc() -> *u8 { 42 as *u8 }
fix Marc() -> mask_t { MaskSingle(Narc) }

pred u32_share(k: lifetime_t, t: thread_id_t, l: *u32) = [_]frac_borrow(k, u32_full_borrow_content(t, l));
lem u32_sync(k: lifetime_t, t: thread_id_t, t1: thread_id_t, l: *u32)
    req [_]u32_share(k, t, l);
    ens [_]u32_share(k, t1, l);
{
    open u32_share(k, t, l);
    produce_lem_ptr_chunk implies_frac(u32_full_borrow_content(t, l), u32_full_borrow_content(t1, l))(){
        open u32_full_borrow_content(t, l)(); assert [?f](*l) |-> _; close [f]u32_full_borrow_content(t1, l)();
    }{
        produce_lem_ptr_chunk implies_frac(u32_full_borrow_content(t1, l), u32_full_borrow_content(t, l))(){
            open u32_full_borrow_content(t1, l)(); assert [?f](*l) |-> _; close [f]u32_full_borrow_content(t, l)();
        }{
            frac_borrow_implies(k, u32_full_borrow_content(t, l), u32_full_borrow_content(t1, l));
        }
    }
    close u32_share(k, t1, l);
    leak u32_share(k,t1, l);
}

lem u32_share_mono(k: lifetime_t, k1: lifetime_t, t: thread_id_t, l: *u32)
    req [_]u32_share(k, t, l) &*& lifetime_inclusion(k1, k) == true;
    ens [_]u32_share(k1, t, l);
{
    open u32_share(k, t, l);
    frac_borrow_mono(k, k1, u32_full_borrow_content(t, l));
    close u32_share(k1, t, l);
    leak u32_share(k1, t, l);
}

pred_ctor dlft_pred(dk: lifetime_t)(gid: isize; destroyed: bool) = ghost_cell(gid, destroyed) &*& if destroyed { true } else { lifetime_token(dk) };

/* While for this concrete Arc type, i.e. ArcU32, we could have the invariant independent of `t`, since in the corresponding generic example we will get
`borrow_end_token(dk, <T>.full_borrow_content(t, &(*ptr).data));` we kept the invariant close to the generic form.
*/
pred_ctor Arc_inv(dk: lifetime_t, gid: isize, ptr: *ArcInnerU32)() = counting(dlft_pred(dk), gid, ?n, ?destroyed) &*&
    if destroyed { true } else { (*ptr).strong |-> ?arc_s &*& std::sync::atomic::AtomicUsize_own(default_tid, arc_s) &*& std::sync::atomic::value(arc_s) == n &*& n >= 1 &*&
    alloc_block(ptr, std::mem::size_of::<ArcInnerU32>()) &*& struct_ArcInnerU32_padding(ptr) &*&
    borrow_end_token(dk, u32_full_borrow_content(default_tid, &(*ptr).data))
    };

pred ArcU32_own(t: thread_id_t, nnp: std::ptr::NonNull<ArcInnerU32>) = [_]exists(?ptr) &*& std::ptr::NonNull_ptr::<ArcInnerU32>(nnp) == ptr &*&
    [_]exists(?dk) &*& [_]exists(?gid) &*& [_]atomic_space(Marc, Arc_inv(dk, gid, ptr)) &*& ticket(dlft_pred(dk), gid, ?frac) &*& [frac]dlft_pred(dk)(gid, false) &*&
    [_]u32_share(dk, default_tid, &(*ptr).data) &*& pointer_within_limits(&(*ptr).data) == true;

pred_ctor Arc_frac_bc(l: *ArcU32, nnp: std::ptr::NonNull<ArcInnerU32>)(;) = (*l).ptr |-> nnp;
pred_ctor ticket_(dk: lifetime_t, gid: isize, frac: real)(;) = ticket(dlft_pred(dk), gid, frac) &*& [frac]ghost_cell(gid, false);

pred ArcU32_share(k: lifetime_t, t: thread_id_t, l: *ArcU32) = [_]exists(?nnp) &*& [_]frac_borrow(k, Arc_frac_bc(l, nnp)) &*&
    [_]exists(?ptr) &*& std::ptr::NonNull_ptr::<ArcInnerU32>(nnp) == ptr &*&
    [_]exists(?dk) &*& [_]exists(?gid) &*& [_]atomic_space(Marc, Arc_inv(dk, gid, ptr)) &*&
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

pred_ctor Ctx(nnp: std::ptr::NonNull<ArcInnerU32>, dk: lifetime_t, gid: isize, l: *ArcU32)() = [_]exists(?ptr) &*& std::ptr::NonNull_ptr::<ArcInnerU32>(nnp) == ptr &*&
        [_]exists(dk) &*& [_]exists(gid) &*& [_]atomic_space(Marc, Arc_inv(dk, gid, ptr)) &*& [_]u32_share(dk, default_tid, &(*ptr).data) &*&
        struct_ArcU32_padding(l);

lem ArcU32_fbor_split(k: lifetime_t, t: thread_id_t, l: *ArcU32)
    req atomic_mask(Nlft) &*& [?qk]lifetime_token(k) &*& full_borrow(k, ArcU32_full_borrow_content(t, l));
    ens atomic_mask(Nlft) &*& [qk]lifetime_token(k) &*&
        [_]exists(?nnp) &*& full_borrow(k, Arc_frac_bc(l, nnp)) &*&
        [_]exists(?ptr) &*& std::ptr::NonNull_ptr::<ArcInnerU32>(nnp) == ptr &*&
        [_]exists(?dk) &*& [_]exists(?gid) &*& [_]atomic_space(Marc, Arc_inv(dk, gid, ptr)) &*&
        [_]exists(?frac) &*& full_borrow(k, ticket_(dk, gid, frac)) &*& full_borrow(k, lifetime_token_(frac, dk)) &*& [_]u32_share(dk, default_tid, &(*ptr).data) &*&
        pointer_within_limits(&(*ptr).data) == true;
{
    let klong = open_full_borrow_strong_m(k, ArcU32_full_borrow_content(t, l), qk);
    open ArcU32_full_borrow_content(t, l)();
    open ArcU32_own(t, ?nnp);
    assert [_]exists::<lifetime_t>(?dk) &*& ticket(_, ?gid, ?frac);
    close Arc_frac_bc(l, nnp)();
    close sep(ticket_(dk, gid, frac), lifetime_token_(frac, dk))();
    close sep(Arc_frac_bc(l, nnp), sep(ticket_(dk, gid, frac), lifetime_token_(frac, dk)))();
    produce_lem_ptr_chunk full_borrow_convert_strong(
        Ctx(nnp, dk, gid, l), sep(Arc_frac_bc(l, nnp), sep(ticket_(dk, gid, frac), lifetime_token_(frac, dk))), klong, ArcU32_full_borrow_content(t, l))() {
            open sep(Arc_frac_bc(l, nnp), sep(ticket_(dk, gid, frac), lifetime_token_(frac, dk)))();
            open Arc_frac_bc(l, nnp)();
            open sep(ticket_(dk, gid, frac), lifetime_token_(frac, dk))();
            open ticket_(dk, gid, frac)();
            open Ctx(nnp, dk, gid, l)();
            close ArcU32_own(t, nnp);
            close ArcU32_full_borrow_content(t, l)();
        }{
            leak exists(nnp);
            close Ctx(nnp, dk, gid, l)();
            close_full_borrow_strong_m(klong, ArcU32_full_borrow_content(t, l), sep(Arc_frac_bc(l, nnp), sep(ticket_(dk, gid, frac), lifetime_token_(frac, dk))));
        }
        full_borrow_mono(klong, k, sep(Arc_frac_bc(l, nnp), sep(ticket_(dk, gid, frac), lifetime_token_(frac, dk))));
        full_borrow_split_m(k, Arc_frac_bc(l, nnp), sep(ticket_(dk, gid, frac), lifetime_token_(frac, dk)));
        full_borrow_split_m(k, ticket_(dk, gid, frac), lifetime_token_(frac, dk));
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
@*/

unsafe impl Send for ArcU32 {}
unsafe impl Sync for ArcU32 {}
/*@
/*
lem bor_end_token_t_indep(k: lifetime_t, t: thread_id_t, t1: thread_id_t, l: *u32)
    req borrow_end_token(k, u32_full_borrow_content(t, l));
    ens borrow_end_token(k, u32_full_borrow_content(t1, l));
{
    produce_lem_ptr_chunk implies(u32_full_borrow_content(t, l), u32_full_borrow_content(t1, l))() {
        open u32_full_borrow_content(t, l)();
        close u32_full_borrow_content(t1, l)();
    }{
        produce_lem_ptr_chunk implies(u32_full_borrow_content(t1, l), u32_full_borrow_content(t, l))(){
            open u32_full_borrow_content(t1, l)();
            close u32_full_borrow_content(t, l)();
        }{
            borrow_end_token_implies(k, u32_full_borrow_content(t, l), u32_full_borrow_content(t1, l));
        }
    }
}
*/
lem ArcU32_send(t: thread_id_t, t1: thread_id_t)
    req ArcU32_own(t, ?nnp);
    ens ArcU32_own(t1, nnp);
{
    open ArcU32_own(t, nnp);
/*    assert [_]exists::<lifetime_t>(?dk) &*& [_]exists::<isize>(?gid) &*& [_]exists::<*ArcInnerU32>(?ptr);
    produce_lem_ptr_chunk implies(Arc_inv(dk, gid, ptr, t), Arc_inv(dk, gid, ptr, t1))(){
        open Arc_inv(dk, gid, ptr, t)();
        assert counting(dlft_pred(dk), gid, _, ?destroyed);
        if destroyed {} else { bor_end_token_t_indep(dk, t, t1, &(*ptr).data); }
        close Arc_inv(dk, gid, ptr, t1)();
    }{
        produce_lem_ptr_chunk implies(Arc_inv(dk, gid, ptr, t1), Arc_inv(dk, gid, ptr, t))(){
            open Arc_inv(dk, gid, ptr, t1)();
            assert counting(_, _, _, ?destroyed);
            if destroyed {} else { bor_end_token_t_indep(dk, t1, t, &(*ptr).data); }
            close Arc_inv(dk, gid, ptr, t)();
        }{
            atomic_space_implies(Marc, Arc_inv(dk, gid, ptr, t), Arc_inv(dk, gid, ptr, t1));
        }
    }
    u32_sync(dk, t, t1, &(*ptr).data);
*/
    close ArcU32_own(t1, nnp);
}

lem ArcU32_sync(k: lifetime_t, t: thread_id_t, t1: thread_id_t, l: *ArcU32)
    req [_]ArcU32_share(k, t, l);
    ens [_]ArcU32_share(k, t1, l);
{
    open ArcU32_share(k, t, l);
    close ArcU32_share(k, t1, l);
    leak ArcU32_share(k, t1, l);
}
@*/
struct ArcInnerU32 {
    strong: AtomicUsize,
    // weak: AtomicUsize,
    data: u32,
}

// TODO: There will be no need to generate proof obligations for internal types
unsafe impl Send for ArcInnerU32 {}
unsafe impl Sync for ArcInnerU32 {}

impl ArcU32 {
    pub fn new(data: u32) -> ArcU32 {
        unsafe {
            let l = std::alloc::Layout::new::<ArcInnerU32>();
            let p = std::alloc::alloc(l) as *mut ArcInnerU32;
            if p.is_null() {
                std::alloc::handle_alloc_error(l);
            }
            //@ close_struct(p);

            *p = ArcInnerU32 {
                strong: AtomicUsize::new(1),
                data,
            };
            let ret = Self {
                ptr: NonNull::new_unchecked(p),
            };
            //@ let nnp = ret.ptr;
            //@ let dk = begin_lifetime();
            //@ leak exists(dk);
            //@ let gid = create_ghost_cell(false); //destroyed
            //@ leak exists::<isize>(gid);
            //@ close dlft_pred(dk)(gid, false);
            //@ start_counting(dlft_pred(dk), gid);
            //@ let frac = create_ticket(dlft_pred(dk), gid);
            //@ close u32_full_borrow_content(default_tid, &(*p).data)();
            //@ borrow(dk, u32_full_borrow_content(default_tid, &(*p).data));
            //@ assert std::sync::atomic::AtomicUsize_own(_t, ?s);
            //@ std::sync::atomic::AtomicUsize_send(_t, default_tid, s);
            //@ close Arc_inv(dk, gid, p)();
            //@ create_atomic_space(Marc, Arc_inv(dk, gid, p));
            //@ full_borrow_into_frac(dk, u32_full_borrow_content(default_tid, &(*p).data));
            //@ leak exists(p);
            //@ close u32_share(dk, default_tid, &(*p).data);
            //@ leak u32_share(_, _, _);
            //@ close ArcU32_own(_t, nnp);
            ret
        }
    }

    /*@
    lem close_dlft_pred() -> real
        req [?q]ghost_cell(?gid, false) &*& [?q1]lifetime_token(?dk);
        ens [result]dlft_pred(dk)(gid, false) &*& [q - result]ghost_cell(gid, false) &*& [q1 -result]lifetime_token(dk);
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
    pub fn strong_count<'a>(this: &'a Self) -> usize {
        unsafe {
            //@ open ArcU32_share(a, _t, this);
            //@ assert [_]exists::<std::ptr::NonNull<ArcInnerU32>>(?nnp);
            //@ open_frac_borrow(a, Arc_frac_bc(this, nnp), _q_a/2);
            //@ open [?qnnp]Arc_frac_bc(this, nnp)();
            let ret;
            {
                //@ assert [_]exists::<lifetime_t>(?dk) &*& [_]exists::<real>(?frac) &*& [_]exists::<isize>(?gid) &*& [_]exists::<*ArcInnerU32>(?ptr);
                /*@
                pred Pre() = [_]frac_borrow(a, ticket_(dk, gid, frac)) &*& [_]frac_borrow(a, lifetime_token_(frac, dk)) &*& [_q_a/2]lifetime_token(a) &*&
                    [_]atomic_space(Marc, Arc_inv(dk, gid, ptr));
                pred Post(r: usize;) = [_q_a/2]lifetime_token(a);
                @*/
                /*@
                produce_lem_ptr_chunk std::sync::atomic::AtomicUsize_load_ghop(&(*ptr).strong, Pre, Post)(){
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
                    //assert false;
                };
                @*/
                //@ close Pre();
                ret = this.ptr.as_ref().strong.load(Ordering::SeqCst);
                //@ open Post(ret);
            }
            //@ close [qnnp]Arc_frac_bc(this, nnp)();
            //@ close_frac_borrow(qnnp, Arc_frac_bc(this, nnp));
            ret
        }
    }
}

impl std::ops::Deref for ArcU32 {
    type Target = u32;

    fn deref<'a>(&'a self) -> &u32 {
        unsafe {
            //@ open ArcU32_share(a, _t, self);
            //@ assert [_]exists::<std::ptr::NonNull<ArcInnerU32>>(?nnp) &*& [_]exists::<real>(?frac) &*& [_]exists::<lifetime_t>(?dk) &*& [_]exists::<*ArcInnerU32>(?ptr);
            //@ open_frac_borrow(a, Arc_frac_bc(self, nnp), _q_a);
            //@ open [?qnnp]Arc_frac_bc(self, nnp)();
            let ret = &self.ptr.as_ref().data;
            //@ close [qnnp]Arc_frac_bc(self, nnp)();
            //@ close_frac_borrow(qnnp, Arc_frac_bc(self, nnp));
            //@ frac_borrow_lft_incl(a, frac, dk);
            //@ u32_share_mono(dk, a, default_tid, &(*ptr).data);
            //@ u32_sync(a, default_tid, _t, &(*ptr).data);
            //@ open u32_share(a, _t, _);
            ret
        }
    }
}

impl Clone for ArcU32 {
    fn clone<'a>(&'a self) -> ArcU32 {
        //@ open ArcU32_share(a, _t, self);
        //@ assert [_]exists::<std::ptr::NonNull<ArcInnerU32>>(?nnp) &*& [_]exists::<lifetime_t>(?dk) &*& [_]exists::<isize>(?gid) &*& [_]exists::<*ArcInnerU32>(?ptr) &*& [_]exists::<real>(?frac);
        //@ open_frac_borrow(a, Arc_frac_bc(self, nnp), _q_a);
        //@ open Arc_frac_bc(self, nnp)();
        let old_size = unsafe {
            {
            /*@
            pred Pre() = [_]frac_borrow(a, ticket_(dk, gid, frac)) &*& [_]frac_borrow(a, lifetime_token_(frac, dk)) &*& [_q_a/2]lifetime_token(a) &*&
                [_]atomic_space(Marc, Arc_inv(dk, gid, ptr));
            pred Post(r: usize) = [_q_a/2]lifetime_token(a);
            @*/
            /*@
            produce_lem_ptr_chunk std::sync::atomic::AtomicUsize_fetch_add_ghop(&(*ptr).strong, 1, Pre, Post)(){
                open Pre();
                open_atomic_space(Marc, Arc_inv(dk, gid, ptr));
                open Arc_inv(dk, gid, ptr)();
                Arc_is_not_destroyed(dk, frac);
                assert std::sync::atomic::is_AtomicUsize_fetch_add_op(?op, _, _, _, ?Q);
                op();
                //counting
                close Arc_inv(dk, gid, ptr)();
                close_atomic_space(Marc);
                assert Q(?r);
                close Post(r);
            };
            @*/
            }
            self.ptr.as_ref().strong.fetch_add(1, Ordering::SeqCst)
        };
        if old_size > MAX_REFCOUNT {
            //TODO: Why does not std library check for `old_size >= MAX_REFCOUNT`
            abort();
        }
        Self { ptr: self.ptr }
    }
}

impl Drop for ArcU32 {
    fn drop<'a>(&'a mut self) {
        unsafe {
            if self.ptr.as_ref().strong.fetch_sub(1, Ordering::SeqCst) != 1 {
                return;
            }
            // acquire!(self.inner().strong);

            std::ptr::drop_in_place(&mut (*self.ptr.as_ptr()).data)
        }
    }
}
