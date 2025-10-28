use std::{alloc::{dealloc, Layout}, ptr::drop_in_place};
//@ use std::alloc::{alloc_block, Layout};
pub struct Box<T> {
    ptr: *mut T
}

/*@
pred<T> <Box<T>>.own(t, box) = (<T>.full_borrow_content(t, box.ptr))() &*& alloc_block(box.ptr as *u8, Layout::new::<T>());
pred_ctor Box_ptr_field<T>(l: *Box<T>, p: *T)(;) = (*l).ptr |-> p;
pred<T> <Box<T>>.share(k, t, l) = [_]exists(?p) &*& [_]frac_borrow(k, Box_ptr_field(l, p)) &*& [_](<T>.share(k, t, p));
@*/

/*@

lem Box_share_mono<T>(k: lifetime_t, k1: lifetime_t, t: thread_id_t, l: *Box<T>)
    req type_interp::<T>() &*& lifetime_inclusion(k1, k) == true &*& [_](<Box<T>>.share(k, t, l));
    ens type_interp::<T>() &*& [_](<Box<T>>.share(k1, t, l));
{
    assume(false);
}

lem Box_share_full<T>(k: lifetime_t, t: thread_id_t, l: *Box<T>)
    req type_interp::<T>() &*& atomic_mask(MaskTop) &*& full_borrow(k, <Box<T>>.full_borrow_content(t, l)) &*& [?q]lifetime_token(k) &*& ref_origin(l) == l;
    ens type_interp::<T>() &*& atomic_mask(MaskTop) &*& [_](<Box<T>>.share(k, t, l)) &*& [q]lifetime_token(k);
{
    open_full_borrow_strong_m_(k, <Box<T>>.full_borrow_content(t, l));
    open <Box<T>>.full_borrow_content(t, l)();
    open <Box<T>>.own(t, ?b);
    let p = b.ptr;
    {
        pred ctx(;) = alloc_block(p as *u8, Layout::new::<T>());
        produce_lem_ptr_chunk restore_full_borrow_(ctx, sep(Box_ptr_field(l, p), <T>.full_borrow_content(t, p)), <Box<T>>.full_borrow_content(t, l))(){
            open ctx();
            open sep(Box_ptr_field(l, p), <T>.full_borrow_content(t, p))();
            open Box_ptr_field::<T>(l, p)();
            close <Box<T>>.own(t, b);
            close <Box<T>>.full_borrow_content(t, l)();
        }{
            close Box_ptr_field::<T>(l, p)();
            close sep(Box_ptr_field(l, p), <T>.full_borrow_content(t, p))();
            close ctx();
            close_full_borrow_strong_m_();
        }
    }
    full_borrow_split_m(k, Box_ptr_field(l, p), <T>.full_borrow_content(t, p));
    share_full_borrow_m(k, t, p);
    full_borrow_into_frac_m(k, Box_ptr_field(l, p));
    leak exists(p);
    close <Box<T>>.share(k, t, l); leak <Box<T>>.share(k, t, l);
}

lem init_ref_Box<T>(p: *Box<T>)
    req type_interp::<T>() &*& atomic_mask(Nlft) &*& ref_init_perm(p, ?x) &*& [_]Box_share::<T>(?k, ?t, x) &*& [?q]lifetime_token(k);
    ens type_interp::<T>() &*& atomic_mask(Nlft) &*& [q]lifetime_token(k) &*& [_]Box_share::<T>(k, t, p) &*& [_]frac_borrow(k, ref_initialized_(p));
{
    assume(false);
}

@*/

impl<T> Box<T> {

    pub fn deref_mut<'a>(&'a mut self) -> &'a mut T {
        unsafe {
            //@ open_full_borrow_strong_('a, Box_full_borrow_content(_t, self));
            //@ open Box_full_borrow_content::<T>(_t, self)();
            //@ open <Box<T>>.own(_t, ?box);
            let r = &mut *self.ptr;
            /*@
            {
                pred Ctx() = (*self).ptr |-> r &*& std::alloc::alloc_block(r as *u8, std::alloc::Layout::new::<T>());
                produce_lem_ptr_chunk restore_full_borrow_(Ctx, <T>.full_borrow_content(_t, r), Box_full_borrow_content(_t, self))() {
                    open Ctx();
                    close Box_own::<T>(_t, box);
                    close Box_full_borrow_content::<T>(_t, self)();
                } {
                    close Ctx();
                    close_full_borrow_strong_();
                }
            }
            @*/
            r
        }
    }

}

impl<T> Drop for Box<T> {
    fn drop(&mut self) {
        unsafe {
            //@ open <Box<T>>.full_borrow_content(_t, self)();
            //@ open <Box<T>>.own(_t, ?b);
            //@ open_full_borrow_content(_t, b.ptr);
            drop_in_place(self.ptr);
            dealloc(self.ptr as *mut u8, Layout::new::<T>());
        }
    }
}