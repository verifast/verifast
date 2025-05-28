#![feature(trivial_bounds)]
use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};
//@ use std::alloc_block_;

pub struct BoxU8 { ptr: *mut u8 }

//@ pred <BoxU8>.own(t, b;) = *b.ptr |-> ?_ &*& alloc_block_(b.ptr);
/*@
pred <BoxU8>.share(k, t, l) = [_]frac_borrow(k, <BoxU8>.full_borrow_content(t, l));
@*/

/*@
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

pred_ctor ctx(p: *u8)(;) = alloc_block_(p);
lem BoxU8_share_full(k: lifetime_t, t: thread_id_t, l: *BoxU8)
    req atomic_mask(MaskTop) &*& [?q]lifetime_token(k) &*& full_borrow(k, BoxU8_full_borrow_content(t, l));
    ens atomic_mask(MaskTop) &*& [q]lifetime_token(k) &*& [_]BoxU8_share(k, t, l);
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
        if p.is_null() { handle_alloc_error(l); }
        *p = v;
        Self { ptr: p }
    }
}
} // impl BoxU8

impl BoxU8 where BoxU8: Copy { // never the case
pub fn into_inner1(b: BoxU8) -> u8 { // Assuming BoxU8 does not implement destructor
    unsafe {
        let ret = *b.ptr;
        //@ to_u8s_(b.ptr);
        dealloc(b.ptr, Layout::new::<u8>());
        ret
    }
}
} // impl BoxU8

impl BoxU8 {
pub fn set<'a>(this: &'a mut BoxU8, new: u8)
//@ req thread_token(?t) &*& [?qa]lifetime_token('a) &*& full_borrow('a, <BoxU8>.full_borrow_content(t, this));
//@ ens thread_token(t) &*& [qa]lifetime_token('a);
{
//@ open_full_borrow(qa, 'a, <BoxU8>.full_borrow_content(t, this));
//@ open <BoxU8>.full_borrow_content(t, this)();
unsafe { *this.ptr = new; }
//@ close <BoxU8>.full_borrow_content(t, this)();
//@ close_full_borrow(<BoxU8>.full_borrow_content(t, this));
//@ leak full_borrow(_, _);
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

impl BoxU8 {
pub fn deref_mut<'a>(this: &'a mut BoxU8) -> &'a mut u8
/*@ req thread_token(?t) &*& [?qa]lifetime_token('a) &*&
    full_borrow('a, <BoxU8>.full_borrow_content(t, this)); @*/
/*@ ens thread_token(t) &*& [qa]lifetime_token('a) &*&
    full_borrow('a, <u8>.full_borrow_content(t, result)); @*/
{//|produce \verb|req| clause.
/*|\begin{vfHeap}
\vfResAdd{tht(t)}, \vfResAdd{[qa]lft('a)}, \vfResAdd{fbor('a, <BoxU8>.fbc(t, this))}
\end{vfHeap}|*/
//@ open_full_borrow_strong_('a, <BoxU8>.full_borrow_content(t, this));
/*|\begin{vfHeap}
tht(t), \vfResRm{[qa]lft('a)}, \vfResRm{fbor('a, <BoxU8>.fbc(t, this))},
\vfResAdd{<BoxU8>.fbc(t, this)()}, \vfResAdd{close_fbor_tstrong_('a, <BoxU8>.fbc(t, this), qa)}
\end{vfHeap}|*/
//@ open <BoxU8>.full_borrow_content(t, this)();
/*|\begin{vfHeap}
tht(t), close_fbor_tstrong_('a, <BoxU8>.fbc(t, this), qa), \vfResRm{<BoxU8>.fbc(t, this)()},
\vfResAdd{*this |-> b}, \vfResAdd{<BoxU8>.own(t, b)}
\end{vfHeap}|*/
let ret = unsafe { &mut *this.ptr };
//@ open <BoxU8>.own(t, ?b);
/*|\begin{vfHeap}
tht(t), close_fbor_tstrong_('a, <BoxU8>.fbc(t, this), qa), *this |-> b,
\vfResRm{<BoxU8>.own(t, b)}, \vfResAdd{*b.ptr |-> _v}, \vfResAdd{alloc_block_(b.ptr)}
\end{vfHeap}|*/
//@ let p = b.ptr;//|ghost variable
/*@ { //|defining a new predicate in function body needs an extra scope
    pred ctx() = *this |-> b &*& alloc_block_(p);
    /*|producing a proof of \verb|restore_full_borrow_| where \verb|P=<BoxU8>.fbc(t, this)| and \verb|Q=<u8>.fbc(t, p)|.|*/
    produce_lem_ptr_chunk restore_full_borrow_(ctx, <u8>.full_borrow_content(t, p),
        <BoxU8>.full_borrow_content(t, this))()
    { //|the proof of the lemma for which a chunk to be produced.
        //|producing lemma's \verb|req| clause
        /*|\begin{vfHeap}
        \vfResAdd{ctx()}, \vfResAdd{<u8>.fbc(t, p)()}
        \end{vfHeap}|*/
        open u8_full_borrow_content(t, p)(); open ctx();
        close <BoxU8>.own(t, b); close <BoxU8>.full_borrow_content(t, this)();
    }{ //|rest of the \verb|deref_mut|'s body verification
        //|producing lemma pointer chunk
        /*|\begin{vfHeap}
        tht(t), close_fbor_tstrong_('a, <BoxU8>.fbc(t, this), qa), *this |-> b,
        *b.ptr |-> _v, alloc_block_(b.ptr),
        \vfResAdd{is_restore_full_borrow_(lem, ctx, <u8>.fbc(t, p), <BoxU8>.fbc(t, this))}
        \end{vfHeap}|*/
        close ctx(); close u8_full_borrow_content(t, p)();
        /*|\begin{vfHeap}
        tht(t), close_fbor_tstrong_('a, <BoxU8>.fbc(t, this), qa),
        is_restore_full_borrow_(lem, ctx, <u8>.fbc(t, p), <BoxU8>.fbc(t, this)),
        \vfResRm{*this |-> b}, \vfResRm{*b.ptr |-> _v}, \vfResRm{alloc_block_(b.ptr)}, \vfResAdd{ctx()}, \vfResAdd{<u8>.fbc(t, p)()}
        \end{vfHeap}|*/
        close_full_borrow_strong_();
        /*|\begin{vfHeap}
        tht(t), \vfResRm{close_fbor_tstrong_('a, <BoxU8>.fbc(t, this), qa)},
        \vfResRm{is_restore_full_borrow_(lem, ctx, <u8>.fbc(t, p), <BoxU8>.fbc(t, this))},
        \vfResRm{ctx()}, \vfResRm{<u8>.fbc(t, p)()},
        \vfResAdd{is_restore_full_borrow_(lem, ctx, <u8>.fbc(t, p), <BoxU8>.fbc(t, this))},
        \vfResAdd{[qa]lft('a)}, \vfResAdd{fbor('a, <u8>.fbc(t, p))}
        \end{vfHeap}|*/
        //|consuming \verb|is_restore_full_borrow_| chunk.
    }
} @*/
ret
}
}

impl std::ops::DerefMut for BoxU8 {
fn deref_mut<'a>(&'a mut self) -> &'a mut u8 { Self::deref_mut/*@::<'a>@*/(self) }
}

impl BoxU8 {
pub fn deref<'a>(this: &'a BoxU8) -> &'a u8
//@ req [?qa]lifetime_token('a) &*& [_](<BoxU8>.share('a, ?t, this));
//@ ens [qa]lifetime_token('a) &*& [_](<u8>.share('a, t, result));
{
    //@ open BoxU8_share('a, t, this);
    //@ assert [_]exists(?p);
    //@ open_frac_borrow('a, field_ptr_chunk(this, p), qa);
    //@ assert [?qp]field_ptr_chunk(this, p)();
    let r = unsafe { & *this.ptr };
    //@ close_frac_borrow(qp, field_ptr_chunk(this, p));
    //@ close u8_share('a, t, r);
    //@ leak <u8>.share('a, t, r);
    r
}
}

impl std::ops::Deref for BoxU8 {
    type Target = u8;
    fn deref<'a>(&'a self) -> &'a u8 { Self::deref/*@::<'a>@*/(self) }
}