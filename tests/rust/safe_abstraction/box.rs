pub struct Box<T> {
    ptr: *mut T
}

/*@

pred<T> <Box<T>>.own(t, box) = (<T>.full_borrow_content(t, box.ptr))() &*& std::alloc::alloc_block(box.ptr as *u8, std::alloc::Layout::new_::<T>());

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
                pred Ctx() = (*self).ptr |-> r &*& std::alloc::alloc_block(r as *u8, std::alloc::Layout::new_::<T>());
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

