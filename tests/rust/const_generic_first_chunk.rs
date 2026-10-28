// A `first_chunk`-shaped function: `[T; N]` in the return type, `N` as a value, and
// `<[T; N]>.share` obtained from `<[T]>.share`.

unsafe fn first_chunk<'a, T, const N: usize>(s: &'a [T]) -> Option<&'a [T; N]>
//@ req [_](<[T]>.share('a, ?t, s));
//@ ens match result { Option::None => s.len() < int_of_const(typeid(N)), Option::Some(r) => [_](<[T; N]>.share('a, t, r)) };
{
    if s.len() < N {
        None
    } else {
        //@ open slice_share::<T>()('a, t, s);
        //@ array_share_split::<T>('a, t, strip_pointer_metadata(s as pointer) as *T, s.len(), int_of_const(typeid(N)));
        //@ leak array_share::<T>('a, t, (strip_pointer_metadata(s as pointer) as *T) + int_of_const(typeid(N)), s.len() - int_of_const(typeid(N)));
        //@ close Array_share::<T, N>()('a, t, (strip_pointer_metadata(s as pointer) as *T) as *[T; N]);
        //@ leak Array_share::<T, N>()('a, t, _);
        Some(unsafe { &*(s.as_ptr() as *const [T; N]) }) //~ignore_ref_creation
    }
}

/*@
lem array_share_split<T>(k: lifetime_t, t: thread_id_t, l: *T, length: usize, mid: usize)
    req [_]array_share::<T>(k, t, l, length) &*& 0 <= mid &*& mid <= length;
    ens array_share::<T>(k, t, l, mid) &*& array_share::<T>(k, t, l + mid, length - mid);
{
    if mid == 0 {
        close array_share::<T>(k, t, l, 0);
        open array_share::<T>(k, t, l, length);
        close array_share::<T>(k, t, l, length);
    } else {
        open array_share::<T>(k, t, l, length);
        array_share_split::<T>(k, t, l + 1, length - 1, mid - 1);
        leak array_share::<T>(k, t, l + 1, mid - 1);
        close array_share::<T>(k, t, l, mid);
    }
}
@*/

fn main() {}
