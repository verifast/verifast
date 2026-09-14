// Test: shared slice reference (&[T]); ownership is [_]<[T]>.share, per element via <T>.share.
fn test_shared_slice<'a>(s: &'a [u8]) -> &'a [u8]
//@ req [?qa]lifetime_token('a) &*& [_](<[u8]>.share('a, currentThread, s));
//@ ens [qa]lifetime_token('a) &*& [_](<[u8]>.share('a, currentThread, result));
//@ on_unwind_ens false;
{
    s
}

// Test: mutable slice reference (&mut [T]); ownership is full_borrow('a, <[T]>.full_borrow_content(t, s)),
// where <[T]>.full_borrow_content is slice_full_borrow_content: the element array, each element owned.
fn test_mut_slice<'a>(s: &'a mut [u8]) -> &'a mut [u8]
//@ req [?qa]lifetime_token('a) &*& full_borrow('a, <[u8]>.full_borrow_content(currentThread, s));
//@ ens [qa]lifetime_token('a) &*& full_borrow('a, <[u8]>.full_borrow_content(currentThread, result));
//@ on_unwind_ens false;
{
    s
}

// Opening the borrow exposes the element array and per-element ownership.
fn test_mut_slice_open_close<'a>(s: &'a mut [u8])
//@ req thread_token(?t) &*& [?qa]lifetime_token('a) &*& full_borrow('a, <[u8]>.full_borrow_content(t, s));
//@ ens thread_token(t) &*& [qa]lifetime_token('a);
//@ on_unwind_ens false;
{
    //@ open_full_borrow(qa, 'a, <[u8]>.full_borrow_content(t, s));
    //@ open slice_full_borrow_content::<u8>(t, s)();
    //@ assert array::<u8>(s as *u8, s.len(), ?elems) &*& foreach(elems, own::<u8>(t));
    //@ close slice_full_borrow_content::<u8>(t, s)();
    //@ close_full_borrow(<[u8]>.full_borrow_content(t, s));
    //@ leak full_borrow(_, _);
}

// Default (generated) spec for a safe fn taking &mut [T].
fn test_mut_slice_default_spec<'a>(s: &'a mut [u8]) {
    //@ leak full_borrow(_, _);
}
