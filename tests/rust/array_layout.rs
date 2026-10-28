// sizeof/alignof of `[T; N]` reached through a type parameter (lemma instantiation, fixpoint
// unfolding) and the `is_array_of`-style fixpoint over a concrete array type.

/*@
fix sz<C>() -> usize { std::mem::size_of::<C>() }

fix is_array_of<T, Chunk>(n: usize) -> bool {
    0 <= n &&
    std::mem::size_of::<Chunk>() == n * std::mem::size_of::<T>() &&
    std::mem::align_of::<Chunk>() == std::mem::align_of::<T>()
}

lem size_via_type_param()
    req true;
    ens sz::<[u8; 4]>() == 4;
{}

lem literal_chunk()
    req true;
    ens is_array_of::<u8, [u8; 4]>(4) == true;
{}

lem const_chunk<T, N>()
    req 0 <= int_of_const(typeid(N));
    ens is_array_of::<T, [T; N]>(int_of_const(typeid(N))) == true;
{}

lem array_size_align<T, N>()
    req true;
    ens std::mem::size_of::<[T; N]>() == int_of_const(typeid(N)) * std::mem::size_of::<T>() &*& std::mem::align_of::<[T; N]>() == std::mem::align_of::<T>();
{}
@*/

fn main() {}
