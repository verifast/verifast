// verifast_options{ignore_ref_creation disable_overflow_check}

// In a #![no_std] crate (such as alloc), rustc names the traits of projection clauses by
// their core:: path, e.g. <F as core::ops::FnOnce<()>>::Output == T. VeriFast declares
// these traits under std::, so the translator must canonicalize the trait name.

#![no_std]

unsafe fn call_fnonce<T, F: FnOnce() -> T>(f: F) -> T
//@ req thread_token(?t) &*& <F>.own(t, f);
//@ ens thread_token(t) &*& <T>.own(t, result);
//@ on_unwind_ens thread_token(t);
{
    //@ close_tuple_0_own(t);
    f()
}

unsafe fn sum<I: Iterator<Item = usize>>(i: &mut I) -> usize
//@ req thread_token(?t) &*& *i |-> ?i0 &*& <I>.own(t, i0);
//@ ens thread_token(t) &*& *i |-> ?i1 &*& <I>.own(t, i1);
//@ on_unwind_ens thread_token(t) &*& *i |-> ?i1 &*& <I>.own(t, i1);
{
    let mut result = 0;
    loop {
        //@ inv thread_token(t) &*& *i |-> ?i1 &*& <I>.own(t, i1);

        match i.next() {
            None => {
                //@ leak <std::option::Option<usize>>.own(_, _);
                return result;
            }
            Some(v) => {
                //@ leak <std::option::Option<usize>>.own(_, _);
                result += v;
            }
        }
    }
}
