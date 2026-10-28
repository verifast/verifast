// `[T; N]` with a const generic `N` in the signature of a specified function.

unsafe fn first_chunk_ptr<T, const N: usize>(s: &[T]) -> *const [T; N]
//@ req true;
//@ ens true;
{
    s.as_ptr() as *const [T; N]
}

fn main() {}
