#![feature(trivial_bounds)]
use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};
//@ use std::alloc_block_;

pub struct BoxU8 { ptr: *mut u8 }

//@ pred <BoxU8>.own(t, b;) = *b.ptr |-> ?_ &*& alloc_block_(b.ptr);
/*@
pred_ctor field_ptr_chunk(l: *BoxU8, p: *u8)(;) = (*l).ptr |-> p;
pred <BoxU8>.share(k, t, l) = [_]exists(?p) &*& [_]frac_borrow(k, field_ptr_chunk(l, p)) &*& [_]frac_borrow(k, u8_full_borrow_content(t, p));
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

/*impl Drop for BoxU8 {
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
}*/

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

impl BoxU8 {
pub fn deref_mut<'a>(this: &'a mut BoxU8) -> &'a mut u8
/*@ req thread_token(?t) &*& [?qa]lifetime_token('a) &*&
    full_borrow('a, <BoxU8>.full_borrow_content(t, this)); @*/
/*@ ens thread_token(t) &*& [qa]lifetime_token('a) &*&
    full_borrow('a, <u8>.full_borrow_content(t, result)); @*/
{
/*$\vfNote{produce \texttt{req} clause}$*/
/*$\vfHeap{\vfResAdd{thread\_token(t)}, \vfResAdd{[qa]lifetime\_token('a)}, \vfResAdd{full\_borrow('a, \tl{}BoxU8\tg{}.full\_borrow\_content(t, this))}}$*/
//@ open_full_borrow_strong_('a, <BoxU8>.full_borrow_content(t, this));
/*$\vfHeap{thread\_token(t), \vfResRm{[qa]lifetime\_token('a)}, \vfResRm{full\_borrow('a, \tl{}BoxU8\tg{}.full\_borrow\_content(t, this))},}$
$\vfState{}{\vfResAdd{\tl{}BoxU8\tg{}.full\_borrow\_content(t, this)()},}$
$\vfState{}{\vfResAdd{close\_full\_borrow\_token\_strong\_('a, \tl{}BoxU8\tg{}.full\_borrow\_content(t, this), qa)}}$*/
//@ open <BoxU8>.full_borrow_content(t, this)();
/*$\vfHeap{thread\_token(t), close\_full\_borrow\_token\_strong\_('a, \tl{}BoxU8\tg{}.full\_borrow\_content(t, this), qa),}$
$\vfState{}{\vfResRm{\tl{}BoxU8\tg{}.full\_borrow\_content(t, this)()}, \vfResAdd{*this |-> b}, \vfResAdd{\tl{}BoxU8\tg{}.own(t, b)}}$*/
let ret = unsafe { &mut *this.ptr };
//@ open <BoxU8>.own(t, ?b);
/*$\vfHeap{thread\_token(t), close\_full\_borrow\_token\_strong\_('a, \tl{}BoxU8\tg{}.full\_borrow\_content(t, this), qa),}$
$\vfState{}{*this |-> b, \vfResRm{\tl{}BoxU8\tg{}.own(t, b)}, \vfResAdd{*b.ptr |-> \_v}, \vfResAdd{alloc\_block\_(b.ptr)}}$*/
//@ let p = b.ptr; //$\vfNote{ghost variable}$
/*@ { //$\vfNote{defining a new predicate in function body needs an extra scope}$
pred ctx() = *this |-> b &*& alloc_block_(p);
/*$\vfNote{producing a proof of \texttt{restore\_full\_borrow\_} with }\vfState{}{P=\tl{}BoxU8\tg{}.full\_borrow\_content(t, this)}\vfNote{ and }$
$\vfState{}{Q=\tl{}u8\tg{}.full\_borrow\_content(t, p)}\vfNote{.}$*/
produce_lem_ptr_chunk restore_full_borrow_(ctx, <u8>.full_borrow_content(t, p),
    <BoxU8>.full_borrow_content(t, this))()
{ //$\vfNote{the proof of the lemma for which a chunk to be produced}$
    //$\vfNote{producing lemma's \texttt{req} clause}$
    //$\vfHeap{\vfResAdd{ctx()}, \vfResAdd{\tl{}u8\tg{}.full\_borrow\_content(t, p)()}}$
    open u8_full_borrow_content(t, p)(); open ctx();
    close <BoxU8>.own(t, b); close <BoxU8>.full_borrow_content(t, this)();
}{ //$\vfNote{rest of the \texttt{deref\_mut}'s body verification}$
    //$\vfNote{producing lemma pointer chunk}$
    /*$\vfHeap{thread\_token(t),}$
    $\vfState{}{close\_full\_borrow\_token\_strong\_('a, \tl{}BoxU8\tg{}.full\_borrow\_content(t, this), qa),}$
    $\vfState{}{*this |-> b, *b.ptr |-> \_v, alloc\_block\_(b.ptr),}$
    $\vfState{}{\vfResAdd{is\_restore\_full\_borrow\_(lem, ctx, \tl{}u8\tg{}.full\_borrow\_content(t, p),}}\hookleftarrow$
        $\vfState{}{\vfResAdd{\tl{}BoxU8\tg{}.full\_borrow\_content(t, this))}}$*/
    close ctx(); close u8_full_borrow_content(t, p)();
    /*$\vfHeap{thread\_token(t),}$
    $\vfState{}{close\_full\_borrow\_token\_strong\_('a, \tl{}BoxU8\tg{}.full\_borrow\_content(t, this), qa),}$
    $\vfState{}{is\_restore\_full\_borrow\_(lem, ctx, \tl{}u8\tg{}.full\_borrow\_content(t, p),}\hookleftarrow$
        $\vfState{}{\tl{}BoxU8\tg{}.full\_borrow\_content(t, this)), \vfResRm{*this |-> b}, \vfResRm{*b.ptr |-> \_v}, \vfResRm{alloc\_block\_(b.ptr)},}$
    $\vfState{}{\vfResAdd{ctx()}, \vfResAdd{\tl{}u8\tg{}.full\_borrow\_content(t, p)()}}$*/
    close_full_borrow_strong_();
    /*$\vfHeap{thread\_token(t),}$
    $\vfState{}{\vfResRm{close\_full\_borrow\_token\_strong\_('a, \tl{}BoxU8\tg{}.full\_borrow\_content(t, this), qa)},}$
    $\vfState{}{\vfResRm{is\_restore\_full\_borrow\_(lem, ctx, \tl{}u8\tg{}.full\_borrow\_content(t, p),}}\hookleftarrow$
        $\vfState{}{\vfResRm{\tl{}BoxU8\tg{}.full\_borrow\_content(t, this))}, \vfResRm{ctx()}, \vfResRm{\tl{}u8\tg{}.full\_borrow\_content(t, p)()},}$
    $\vfState{}{\vfResAdd{is\_restore\_full\_borrow\_(lem, ctx, \tl{}u8\tg{}.full\_borrow\_content(t, p),}}\hookleftarrow$
        $\vfState{}{\vfResAdd{\tl{}BoxU8\tg{}.full\_borrow\_content(t, this))},}$
    $\vfState{}{\vfResAdd{[qa]lifetime\_token('a)}, \vfResAdd{full\_borrow('a, \tl{}u8\tg{}.full\_borrow\_content(t, p))}}$*/
    //$\vfNote{consuming \texttt{is\_restore\_full\_borrow\_} chunk}$
}
} @*/
ret
}
}

impl std::ops::DerefMut for BoxU8 {
fn deref_mut<'a>(&'a mut self) -> &'a mut u8 { Self::deref_mut/*@::<'a>@*/(self) }
}
