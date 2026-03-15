// Test: shared slice reference (&[T])
fn test_shared_slice<'a>(s: &'a [u8]) -> &'a [u8]
//@ req [?qa]lifetime_token('a) &*& [_](<[u8]>.share('a, currentThread, s));
//@ ens [qa]lifetime_token('a) &*& [_](<[u8]>.share('a, currentThread, result));
//@ on_unwind_ens false;
{
    s
}

// Test: mutable slice reference (&mut [T])
fn test_mut_slice<'a>(s: &'a mut [u8]) -> u32
//@ req thread_token(currentThread) &*& *s |-> ?_;
//@ ens thread_token(currentThread) &*& *s |-> _;
//@ on_unwind_ens false;
{
    0
}
