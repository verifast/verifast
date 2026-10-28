// The const-generic bodies call `__VeriFast_wrapper` helpers (inlined by the checker), which
// requires accepting the `ConstArgHasType` clause of `N` and the `N` operand.

fn lt_n__VeriFast_wrapper(x: usize, n: usize) -> bool {
    x < n
}

fn lt_n<const N: usize>(x: usize) -> bool {
    lt_n__VeriFast_wrapper(x, N)
}

unsafe fn first_chunk_ptr<T, const N: usize>(s: &[T]) -> *const [T; N] {
    s.as_ptr() as *const [T; N]
}
