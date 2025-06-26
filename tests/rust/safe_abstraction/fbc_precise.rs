struct Foo();
//@ pred <Foo>.own(t, f;) = true;
//@ pred own_is_precise<T>(p: pred(thread_id_t, T;)) = true;
//@ pred fbc_is_precise<T>(p: fix (thread_id_t, *T, pred(;)));
//@ pred Foo_own_is_precise(t: thread_id_t, f: Foo) = own_is_precise(<Foo>.own);
//@ pred Foo_fbc_is_precise() = fbc_is_precise(<Foo>.full_borrow_content);

impl Drop for Foo {
    fn drop(&mut self) {}
}

mod bar {
    struct Bar();
}
//@ pred <bar::Bar>.own(t, f;) = true;
//@ pred bar::Bar_own_is_precise(t: thread_id_t, b: bar::Bar) = own_is_precise(<bar::Bar>.own);
//@ pred bar::Bar_fbc_is_precise() = fbc_is_precise(<bar::Bar>.full_borrow_content);

mod baz {
    //@ use bar::*;
    //@ pred Bar_own_is_precise(t: thread_id_t, b: Bar) = own_is_precise(<Bar>.own);
    //@ pred Bar_fbc_is_precise() = fbc_is_precise(<Bar>.full_borrow_content);
}

/*@
pred primitive_types_own_is_precise(t: thread_id_t) =
    own_is_precise(<bool>.own) &*&
    // own_is_precise(<char>.own) &*&
    own_is_precise(<*_>.own) &*&
    own_is_precise(<u8>.own) &*&
    own_is_precise(<u16>.own) &*&
    own_is_precise(<u32>.own) &*&
    own_is_precise(<u64>.own) &*&
    own_is_precise(<u128>.own) &*&
    own_is_precise(<usize>.own) &*&
    own_is_precise(<i8>.own) &*&
    own_is_precise(<i16>.own) &*&
    own_is_precise(<i32>.own) &*&
    own_is_precise(<i64>.own) &*&
    own_is_precise(<i128>.own) &*&
    own_is_precise(<isize>.own);

pred primitive_types_fbc_is_precise() =
    fbc_is_precise(<bool>.full_borrow_content) &*&
    // fbc_is_precise(<char>.full_borrow_content) &*&
    fbc_is_precise(<*_>.full_borrow_content) &*&
    fbc_is_precise(<u8>.full_borrow_content) &*&
    fbc_is_precise(<u16>.full_borrow_content) &*&
    fbc_is_precise(<u32>.full_borrow_content) &*&
    fbc_is_precise(<u64>.full_borrow_content) &*&
    fbc_is_precise(<u128>.full_borrow_content) &*&
    fbc_is_precise(<usize>.full_borrow_content) &*&
    fbc_is_precise(<i8>.full_borrow_content) &*&
    fbc_is_precise(<i16>.full_borrow_content) &*&
    fbc_is_precise(<i32>.full_borrow_content) &*&
    fbc_is_precise(<i64>.full_borrow_content) &*&
    fbc_is_precise(<i128>.full_borrow_content) &*&
    fbc_is_precise(<isize>.full_borrow_content);
@*/
