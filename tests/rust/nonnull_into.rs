// The identity conversion `NonNull<T> -> NonNull<T>` (via `impl<T> From<T> for T`) returns its
// argument. `alloc::raw_vec` relies on this since `RawVecInner::ptr` became a `NonNull<u8>`.

use std::ptr::NonNull;

unsafe fn identity_into(p: NonNull<u8>) -> NonNull<u8>
//@ req true;
//@ ens result == p;
{
    p.into()
}

fn main() {}
