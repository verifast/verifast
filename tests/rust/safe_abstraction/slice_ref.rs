// Test: shared slice reference (&[T]); ownership is [_]<[T]>.share, per element via <T>.share.
fn test_shared_slice<'a>(s: &'a [u8]) -> &'a [u8]
//@ req [?qa]lifetime_token('a) &*& [_](<[u8]>.share('a, currentThread, s));
//@ ens [qa]lifetime_token('a) &*& [_](<[u8]>.share('a, currentThread, result));
//@ on_unwind_ens false;
{
    s
}
