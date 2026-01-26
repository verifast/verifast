use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};
//@ use std::alloc_block_;

pub struct Box<T> { ptr: *mut T }

/*@
pred<T> <Box<T>>.own(t, b) = *b.ptr |-> ?v &*& <T>.own(t, v) &*& alloc_block_(b.ptr);
pred_ctor Box_ptr_field<T>(l: *Box<T>, p: *T)(;) = (*l).ptr |-> p;
pred<T> <Box<T>>.share(k, t, l) = [_]exists(?p) &*&
    [_]frac_borrow(k, Box_ptr_field(l, p)) &*& [_](<T>.share(k, t, p));

lem Box_share_mono<T>(k: lifetime_t, k1: lifetime_t, t: thread_id_t, l: *Box<T>)
    req type_interp::<T>() &*& lifetime_inclusion(k1, k) == true &*&
        [_](<Box<T>>.share(k, t, l));
    ens type_interp::<T>() &*& [_](<Box<T>>.share(k1, t, l));
{
    open <Box<T>>.share(k, t, l); assert [_]exists(?p);
    /*|\begin{vfHeap}
    \vfResAdd{type_interp::<T>()}, \vfResAdd{[_]exists(p)}, \vfResAdd{[_]fcbor(k, Box_ptr_field(l, p))},
    \vfResAdd{[_](<T>.share(k, t, p))}
    \end{vfHeap}|*/
    frac_borrow_mono(k, k1, Box_ptr_field(l, p));
    /*|\begin{vfHeap}
    type_interp::<T>(), [_]exists(p), [_](<T>.share(k, t, p)),
    \vfResRm{[_]fcbor(k, Box_ptr_field(l, p))}, \vfResAdd{[_]fcbor(k1, Box_ptr_field(l, p))}
    \end{vfHeap}|*/
    share_mono(k, k1, t, p); //| Requires and ensures \verb|type_interp::<T>()|
    /*|\begin{vfHeap}
    \vfResAssert{type_interp::<T>()}, [_]exists(p), [_]fcbor(k1, Box_ptr_field(l, p)),
    \vfResRm{[_](<T>.share(k, t, p))}, \vfResAdd{[_](<T>.share(k1, t, p))}
    \end{vfHeap}|*/
    close <Box<T>>.share(k1, t, l);
    leak <Box<T>>.share(k1, t, l);
}

lem Box_share_full<T>(k: lifetime_t, t: thread_id_t, l: *Box<T>)
    req type_interp::<T>() &*& atomic_mask(MaskTop) &*& [?q]lifetime_token(k) &*&
        full_borrow(k, <Box<T>>.full_borrow_content(t, l));
    ens type_interp::<T>() &*& atomic_mask(MaskTop) &*& [q]lifetime_token(k) &*&
        [_](<Box<T>>.share(k, t, l));
{
    open_full_borrow_strong_m_(k, <Box<T>>.full_borrow_content(t, l));
    open <Box<T>>.full_borrow_content(t, l)();
    open <Box<T>>.own(t, ?b);
    let p = b.ptr;
    {
        pred ctx(;) = alloc_block_(p);
        produce_lem_ptr_chunk restore_full_borrow_(ctx,
            sep(Box_ptr_field(l, p), <T>.full_borrow_content(t, p)),
            <Box<T>>.full_borrow_content(t, l))()
        {
            open ctx();
            open sep(Box_ptr_field(l, p), <T>.full_borrow_content(t, p))();
            open Box_ptr_field::<T>(l, p)();
            /*|\begin{vfHeap}
            \vfResAdd{alloc_block_(p)}, \vfResAdd{(*l).ptr |-> p}, \vfResAdd{<T>.fbc(t, p)()}
            \end{vfHeap}|*/
            open_full_borrow_content::<T>(t, p);
            /*|\begin{vfHeap}
            alloc_block_(p), (*l).ptr |-> p, \vfResRm{<T>.fbc(t, p)()},
            \vfResAdd{*p |-> v}, \vfResAdd{<T>.own(t, v)}
            \end{vfHeap}|*/
            close <Box<T>>.own(t, b);
            close <Box<T>>.full_borrow_content(t, l)();
        }{
            close ctx();
            /*|\begin{vfHeap}
            ..., \vfResAdd{*p |-> v}, \vfResAdd{<T>.own(t, v)}
            \end{vfHeap}|*/
            close_full_borrow_content::<T>(t, p);
            /*|\begin{vfHeap}
            ..., \vfResRm{*p |-> v}, \vfResRm{<T>.own(t, v)}, \vfResAdd{<T>.fbc(t, p)()}
            \end{vfHeap}|*/
            close Box_ptr_field::<T>(l, p)();
            close sep(Box_ptr_field(l, p), <T>.full_borrow_content(t, p))();
            close_full_borrow_strong_m_();
        }
    }
    full_borrow_split_m(k, Box_ptr_field(l, p), <T>.full_borrow_content(t, p));
    /*|\begin{vfHeap}
    ..., type_interp::<T>(), \vfResAdd{[q]lft(k)},
    \vfResAdd{fbor(k, Box_ptr_field(l, p))}, \vfResAdd{fbor(k, <T>.fbc(t, p))}
    \end{vfHeap}|*/
    full_borrow_into_frac_m(k, Box_ptr_field(l, p));
    /*|\begin{vfHeap}
    ..., type_interp::<T>(), [q]lft(k), fbor(k, <T>.fbc(t, p)),
    \vfResRm{fbor(k, Box_ptr_field(l, p))}, \vfResAdd{[_]fcbor(k, Box_ptr_field(l, p))}
    \end{vfHeap}|*/
    share_full_borrow_m::<T>(k, t, p); //| Requires and ensures \verb|type_interp::<T>() &*& [q]lft(k)|
    /*|\begin{vfHeap}
    ..., \vfResAssert{type_interp::<T>()}, \vfResAssert{[q]lft(k)}, [_]fcbor(k, Box_ptr_field(l, p)),
    \vfResRm{fbor(k, <T>.fbc(t, p))}, \vfResAdd{[_](<T>.share(k, t, p))}
    \end{vfHeap}|*/
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

    pub fn set(& mut self, new: T) {
        unsafe {
            //@ open <Box<T>>.own(_t, ?b);
            *self.ptr = new;
            //@ close <Box<T>>.own(_t, b);
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
        //@ open_frac_borrow('a, Box_ptr_field(self, p), _q_a);
        //@ open [?qp]Box_ptr_field::<T>(self, p)();
        let r = unsafe { &*self.ptr };
        //@ close [qp]Box_ptr_field::<T>(self, p)();
        //@ close_frac_borrow(qp, Box_ptr_field(self, p));
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
                pred ctx(;) = (*self).ptr |-> r &*& alloc_block_(r);
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
