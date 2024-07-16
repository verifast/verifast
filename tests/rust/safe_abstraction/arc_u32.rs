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

pred u32_share(k: lifetime_t, t: thread_id_t, l: *u32) = frac_borrow(k, u32_full_borrow_content(t, l));

pred_ctor dlft_pred(dk: lifetime_t)(gid: isize; destroyed: bool) = ghost_cell(gid, destroyed) &*& if destroyed { true } else { lifetime_token(dk) };
pred_ctor Arc_inv(dk: lifetime_t, gid: isize, ptr: *ArcInnerU32, t: thread_id_t)() = counting(dlft_pred(dk), gid, ?n, ?destroyed) &*&
    if destroyed { true } else { (*ptr).strong |-> ?arc_s &*& *(&(*ptr).strong as *usize) == n &*& n >= 1 &*&
    alloc_block(ptr, std::mem::size_of::<ArcInnerU32>()) &*& struct_ArcInnerU32_padding(ptr) &*&
    borrow_end_token(dk, u32_full_borrow_content(t, &(*ptr).data))
    };

pred ArcU32_own(t: thread_id_t, nnp: std::ptr::NonNull<ArcInnerU32>) = [_]exists(?ptr) &*& std::ptr::NonNull_ptr::<ArcInnerU32>(nnp) == ptr &*&
    [_]exists(?dk) &*& [_]exists(?gid) &*& [_]atomic_space(Marc, Arc_inv(dk, gid, ptr, t)) &*& ticket(dlft_pred(dk), gid, ?frac) &*& [frac]dlft_pred(dk)(gid, false) &*&
    [_]u32_share(dk, t, &(*ptr).data);

pred_ctor Arc_frac_bc(l: *ArcU32, nnp: std::ptr::NonNull<ArcInnerU32>)(;) = (*l).ptr |-> nnp;
pred_ctor ticket_(dk: lifetime_t, gid: isize, frac: real)(;) = ticket(dlft_pred(dk), gid, frac) &*& [frac]ghost_cell(gid, false);

pred ArcU32_share(k: lifetime_t, t: thread_id_t, l: *ArcU32) = [_]exists(?nnp) &*& [_]frac_borrow(k, Arc_frac_bc(l, nnp)) &*&
    [_]exists(?ptr) &*& std::ptr::NonNull_ptr::<ArcInnerU32>(nnp) == ptr &*&
    [_]exists(?dk) &*& [_]exists(?gid) &*& [_]atomic_space(Marc, Arc_inv(dk, gid, ptr, t)) &*&
    [_]exists(?frac) &*& [_]frac_borrow(k, ticket_(dk, gid, frac)) &*& [_]frac_borrow(k, lifetime_token_(frac, dk)) &*& [_]u32_share(dk, t, &(*ptr).data);

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

pred_ctor Ctx(nnp: std::ptr::NonNull<ArcInnerU32>, dk: lifetime_t, gid: isize, t: thread_id_t, l: *ArcU32)() = [_]exists(?ptr) &*& std::ptr::NonNull_ptr::<ArcInnerU32>(nnp) == ptr &*&
        [_]exists(dk) &*& [_]exists(gid) &*& [_]atomic_space(Marc, Arc_inv(dk, gid, ptr, t)) &*& [_]u32_share(dk, t, &(*ptr).data) &*&
        struct_ArcU32_padding(l);

lem ArcU32_fbor_split(k: lifetime_t, t: thread_id_t, l: *ArcU32)
    req atomic_mask(Nlft) &*& [?qk]lifetime_token(k) &*& full_borrow(k, ArcU32_full_borrow_content(t, l));
    ens atomic_mask(Nlft) &*& [qk]lifetime_token(k) &*&
        [_]exists(?nnp) &*& full_borrow(k, Arc_frac_bc(l, nnp)) &*&
        [_]exists(?ptr) &*& std::ptr::NonNull_ptr::<ArcInnerU32>(nnp) == ptr &*&
        [_]exists(?dk) &*& [_]exists(?gid) &*& [_]atomic_space(Marc, Arc_inv(dk, gid, ptr, t)) &*&
        [_]exists(?frac) &*& full_borrow(k, ticket_(dk, gid, frac)) &*& full_borrow(k, lifetime_token_(frac, dk)) &*& [_]u32_share(dk, t, &(*ptr).data);
{
    let klong = open_full_borrow_strong_m(k, ArcU32_full_borrow_content(t, l), qk);
    open ArcU32_full_borrow_content(t, l)();
    open ArcU32_own(t, ?nnp);
    assert [_]exists::<lifetime_t>(?dk) &*& ticket(_, ?gid, ?frac);
    close Arc_frac_bc(l, nnp)();
    close sep(ticket_(dk, gid, frac), lifetime_token_(frac, dk))();
    close sep(Arc_frac_bc(l, nnp), sep(ticket_(dk, gid, frac), lifetime_token_(frac, dk)))();
    produce_lem_ptr_chunk full_borrow_convert_strong(
        Ctx(nnp, dk, gid, t, l), sep(Arc_frac_bc(l, nnp), sep(ticket_(dk, gid, frac), lifetime_token_(frac, dk))), klong, ArcU32_full_borrow_content(t, l))() {
            open sep(Arc_frac_bc(l, nnp), sep(ticket_(dk, gid, frac), lifetime_token_(frac, dk)))();
            open Arc_frac_bc(l, nnp)();
            open sep(ticket_(dk, gid, frac), lifetime_token_(frac, dk))();
            open ticket_(dk, gid, frac)();
            open Ctx(nnp, dk, gid, t, l)();
            close ArcU32_own(t, nnp);
            close ArcU32_full_borrow_content(t, l)();
        }{
            leak exists(nnp);
            close Ctx(nnp, dk, gid, t, l)();
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
lem ArcU32_send(t: thread_id_t, t1: thread_id_t)
    req ArcU32_own(t, ?nnp);
    ens ArcU32_own(t1, nnp);
{
    open ArcU32_own(t, nnp);
    close ArcU32_own(t1, nnp);
}
@*/
struct ArcInnerU32 {
    strong: AtomicUsize,
    // weak: AtomicUsize,
    data: u32,
}

// TODO: Make sure we do need these markers
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

            *p = ArcInnerU32 {
                strong: AtomicUsize::new(1),
                data,
            };
            Self {
                ptr: NonNull::new_unchecked(p),
            }
        }
    }

    pub fn strong_count<'a>(this: &'a Self) -> usize {
        unsafe { this.ptr.as_ref().strong.load(Ordering::SeqCst) }
    }
}

impl std::ops::Deref for ArcU32 {
    type Target = u32;

    fn deref<'a>(&'a self) -> &u32 {
        unsafe { &self.ptr.as_ref().data }
    }
}

impl Clone for ArcU32 {
    fn clone<'a>(&'a self) -> ArcU32 {
        let old_size = unsafe { self.ptr.as_ref().strong.fetch_add(1, Ordering::SeqCst) };
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
