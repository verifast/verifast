// A const generic parameter used as a value, and a `[T; N]` return type.

fn lt_n<const N: usize>(x: usize) -> bool {
    x < N
}

unsafe fn first_chunk_ptr<T, const N: usize>(s: &[T]) -> *const [T; N] {
    s.as_ptr() as *const [T; N]
}
