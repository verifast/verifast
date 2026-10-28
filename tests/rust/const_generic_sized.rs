// A const generic parameter can instantiate a lemma's type parameter (it counts as Sized).

/*@
lem l<T, N>()
    req true;
    ens true;
{}
@*/

unsafe fn f<T, const N: usize>(x: &[T; N]) -> usize
//@ req true;
//@ ens true;
{
    //@ l::<T, N>();
    N
}

fn main() {}
