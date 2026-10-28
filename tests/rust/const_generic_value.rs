// A const generic parameter used as a value in a specified function: its value is
// `int_of_const(typeid(N))`, and the parameter's range is an implicit precondition.

fn lt_n<const N: usize>(x: usize) -> bool
//@ req true;
//@ ens result == (x < int_of_const(typeid(N)));
{
    x < N
}

unsafe fn helper(n: usize) -> usize
//@ req true;
//@ ens result == n;
{ n }

unsafe fn pass_n<const N: usize>() -> usize
//@ req true;
//@ ens result == int_of_const(typeid(N));
{
    helper(N)
}

fn main() {}
