#![feature(trivial_bounds)]
use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};
//@ use std::alloc_block_;

pub struct BoxU8 { ptr: *mut u8 }

/*@
pred <BoxU8>.own(t, b;) = *b.ptr |-> ?_ &*& alloc_block_(b.ptr);
pred_ctor BoxU8_ptr_field(l: *BoxU8, p: *u8)(;) = (*l).ptr |-> p;
pred <BoxU8>.share(k, t, l) = [_]exists(?p) &*&
    [_]frac_borrow(k, BoxU8_ptr_field(l, p)) &*& [_]frac_borrow(k, <u8>.full_borrow_content(t, p));
@*/

/*@
lem BoxU8_share_mono(k: lifetime_t, k1: lifetime_t, t: thread_id_t, l: *BoxU8)
    req lifetime_inclusion(k1, k) == true &*& [_](<BoxU8>.share(k, t, l));
    ens [_](<BoxU8>.share(k1, t, l));
{
    open <BoxU8>.share(k, t, l);
    assert [_]exists(?p);
    /*|\begin{vfPathCond}
    \vfResAdd{lifetime_inclusion(k1, k) == true}
    \end{vfPathCond}
    \begin{vfHeap}
    \vfResAdd{[_]exists(p)}, \vfResAdd{[_]fcbor(k, BoxU8_ptr_field(l, p))}, \vfResAdd{[_]fcbor(k, <u8>.fbc(t, p))}
    \end{vfHeap}|*/
    frac_borrow_mono(k, k1, BoxU8_ptr_field(l, p));
    /*|\begin{vfPathCond}
    lifetime_inclusion(k1, k) == true
    \end{vfPathCond}
    \begin{vfHeap}
    [_]exists(p), [_]fcbor(k, <u8>.fbc(t, p)),
    \vfResRm{[_]fcbor(k, BoxU8_ptr_field(l, p))}, \vfResAdd{[_]fcbor(k1, BoxU8_ptr_field(l, p))}
    \end{vfHeap}|*/
    frac_borrow_mono(k, k1, <u8>.full_borrow_content(t, p));
    /*|\begin{vfPathCond}
    lifetime_inclusion(k1, k) == true
    \end{vfPathCond}
    \begin{vfHeap}
    [_]exists(p), [_]fcbor(k1, BoxU8_ptr_field(l, p)),
    \vfResRm{[_]fcbor(k, <u8>.fbc(t, p))}, \vfResAdd{[_]fcbor(k1, <u8>.fbc(t, p))}
    \end{vfHeap}|*/
    close BoxU8_share(k1, t, l); leak BoxU8_share(k1, t, l);
}

lem BoxU8_share_full(k: lifetime_t, t: thread_id_t, l: *BoxU8)
    req atomic_mask(MaskTop) &*& [?q]lifetime_token(k) &*&
        full_borrow(k, <BoxU8>.full_borrow_content(t, l));
    ens atomic_mask(MaskTop) &*& [q]lifetime_token(k) &*&
        [_](<BoxU8>.share(k, t, l));
{
    open_full_borrow_strong_m_(k, <BoxU8>.full_borrow_content(t, l));
    open <BoxU8>.full_borrow_content(t, l)();
    open <BoxU8>.own(t, ?b);
    let p = b.ptr;
    {
        pred ctx(;) = alloc_block_(p);
        produce_lem_ptr_chunk restore_full_borrow_(ctx,
                sep(BoxU8_ptr_field(l, p), <u8>.full_borrow_content(t, p)),
                <BoxU8>.full_borrow_content(t, l))() {
            open ctx();
            open sep(BoxU8_ptr_field(l, p), <u8>.full_borrow_content(t, p))();
            open u8_full_borrow_content(t, p)();
            close <BoxU8>.full_borrow_content(t, l)();
        }{
            close ctx(); close u8_full_borrow_content(t, p)();
            close sep(BoxU8_ptr_field(l, p), <u8>.full_borrow_content(t, p))();
            close_full_borrow_strong_m_();
        }
    }
    /*|\begin{vfHeap}
    \vfResAdd{atomic_mask(MaskTop)}, \vfResAdd{[q]lifetime_token(k)},
    \vfResAdd{fbor(k, sep(BoxU8_ptr_field(l, p), <u8>.fbc(t, p)))}
    \end{vfHeap}|*/
    full_borrow_split_m(k, BoxU8_ptr_field(l, p), <u8>.full_borrow_content(t, p));
    /*|\begin{vfHeap}
    atomic_mask(MaskTop), [q]lifetime_token(k),
    \vfResRm{fbor(k, sep(BoxU8_ptr_field(l, p), <u8>.fbc(t, p)))},
    \vfResAdd{fbor(k, BoxU8_ptr_field(l, p))}, \vfResAdd{fbor(k, <u8>.fbc(t, p))}
    \end{vfHeap}|*/
    full_borrow_into_frac_m(k, BoxU8_ptr_field(l, p));
    /*|\begin{vfHeap}
    atomic_mask(MaskTop), [q]lifetime_token(k), fbor(k, <u8>.fbc(t, p)),
    \vfResRm{fbor(k, BoxU8_ptr_field(l, p))}, \vfResAdd{fcbor(k, BoxU8_ptr_field(l, p))}
    \end{vfHeap}|*/
    full_borrow_into_frac_m(k, <u8>.full_borrow_content(t, p));
    leak exists(p);
    /*|\begin{vfHeap}
    atomic_mask(MaskTop), [q]lifetime_token(k), fcbor(k, BoxU8_ptr_field(l, p)),
    \vfResRm{fbor(k, <u8>.fbc(t, p))},
    \vfResAdd{fcbor(k, <u8>.fbc(t, p))}, \vfResAdd{[_]exists(p)}
    \end{vfHeap}|*/
    close BoxU8_share(k, t, l);
    leak BoxU8_share(k, t, l);
}

lem init_ref_BoxU8(p: *BoxU8)
    req atomic_mask(Nlft) &*& ref_init_perm(p, ?x) &*& [_]BoxU8_share(?k, ?t, x) &*& [?q]lifetime_token(k);
    ens atomic_mask(Nlft) &*& [q]lifetime_token(k) &*& [_]BoxU8_share(k, t, p) &*& [_]frac_borrow(k, ref_initialized_(p));
{ assume(false); /* TODO */ }
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
    //@ req thread_token(?t) &*& <BoxU8>.full_borrow_content(t, self)();
    //@ ens thread_token(t) &*& (*self).ptr |-> ?_;
    {
        unsafe {
            //@ open <BoxU8>.full_borrow_content(t, self)();
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
{//|produce \verb|req| clause.
    /*|\begin{vfHeap}
    \vfResAdd{[qa]lft('a)}, \vfResAdd{[_](<BoxU8>.share('a, t, this))}
    \end{vfHeap}|*/
    //@ open BoxU8_share('a, t, this);
    /*|\begin{vfHeap}
    [qa]lft('a), \vfResRm{[_](<BoxU8>.share('a, t, this))}, \vfResAdd{[_]exists(p)},
    \vfResAdd{[_]fcbor('a, BoxU8_ptr_field(this, p))}, \vfResAdd{[_]fcbor('a, <u8>.fbc(t, p))}
    \end{vfHeap}|*/
    //@ assert [_]exists(?p);
    //@ open_frac_borrow('a, BoxU8_ptr_field(this, p), qa);
    /*|\begin{vfHeap}
    [_]exists(p), [_]fcbor('a, <u8>.fbc(t, p)), \vfResRm{[qa]lft('a)},
    \vfResRm{[_]fcbor('a, BoxU8_ptr_field(this, p))}, \vfResAdd{[qp]BoxU8_ptr_field(this, p)()},
    \vfResAdd{close_fcbor_t(qp, BoxU8_ptr_field(this, p), qa, 'a)}
    \end{vfHeap}|*/
    //@ assert [?qp]BoxU8_ptr_field(this, p)();
    let r = unsafe { & *this.ptr };
    //@ close_frac_borrow(qp, BoxU8_ptr_field(this, p));
    /*|\begin{vfHeap}
    ..., [_]fcbor('a, <u8>.fbc(t, p)),
    \vfResRm{close_fcbor_t(qp, BoxU8_ptr_field(this, p), qa, 'a)},
    \vfResRm{[qp]BoxU8_ptr_field(this, p)()}, \vfResAdd{[qa]lft('a)}
    \end{vfHeap}|*/
    //@ close u8_share('a, t, r);
    //@ leak <u8>.share('a, t, r);
    /*|\begin{vfHeap}
    ..., [qa]lft('a), \vfResRm{[_]fcbor('a, <u8>.fbc(t, p))}, \vfResAdd{[_](<u8>.share('a, t, p))}
    \end{vfHeap}|*/
    r
}
}

impl std::ops::Deref for BoxU8 {
    type Target = u8;
    fn deref<'a>(&'a self) -> &'a u8
    //@ req [?qa]lifetime_token('a) &*& [_](<BoxU8>.share('a, ?t, self));
    //@ ens [qa]lifetime_token('a) &*& [_](<u8>.share('a, t, result));
    { Self::deref/*@::<'a>@*/(self) }
}

impl BoxU8 {
pub fn into_inner(b: BoxU8) -> u8
//@ req thread_token(?t) &*& <BoxU8>.own(t, b);
//@ ens thread_token(t);
{
    unsafe {
        //| \verifast{} auto-opens \verb|<BoxU8>.own| to justify \verb|*b.ptr|
        let ret = *b.ptr;
        //@ close <BoxU8>.own(t, b);
        ret
    }
/*|\begin{vfHeap}
\vfResAdd{thread_token(t)}, \vfResAdd{<BoxU8>.own(t, b)}
\end{vfHeap}|*/
//| implicit destructor call for \verb|b|
/*|\begin{vfHeap}
thread_token(t), \vfResRm{<BoxU8>.own(t, b)}
\end{vfHeap}|*/
}
}

unsafe impl Send for BoxU8 {}
unsafe impl Sync for BoxU8 {}

/*@
lem BoxU8_sync(t1: thread_id_t)
    req is_Sync(typeid(BoxU8)) == true &*& [_]BoxU8_share(?k, ?t0, ?l);
    ens [_]BoxU8_share(k, t1, l);
{
    assume(false);
}
@*/