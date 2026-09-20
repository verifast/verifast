// Test for structs and enums with const generic parameters.
// Previously failed with "Structs with const parameters are not yet supported".

#![no_std]
#![allow(dead_code)]

//@ pred foo<T>(x: T) = true;

struct Buf<const N: usize> {
    len: usize,
}

// A const parameter sitting between two type parameters: type and const
// parameters keep their declaration order, so the arguments of
// `Pair<i32, 7, usize>` must line up as T = i32, N = 7, A = usize.
struct Pair<T, const N: usize, A> {
    first: T,
    second: A,
}

struct WithLifetime<'a, T, const N: usize> {
    r: &'a T,
}

enum Choice<T, const N: usize> {
    Left(T),
    Right(usize),
}

// A const parameter of a struct, passed on to another const-generic struct.
struct Outer<const N: usize> {
    inner: Pair<i32, N, usize>,
}

unsafe fn buf_len<const N: usize>(b: Buf<N>) -> usize
//@ req true;
//@ ens foo::<i32>(int_of_const(typeid(N)));
{
    //@ close foo::<i32>(int_of_const(typeid(N)));
    b.len
}

unsafe fn pair_first<const N: usize>(p: Pair<i32, N, usize>) -> i32
//@ req true;
//@ ens foo::<i32>(int_of_const(typeid(N)));
{
    //@ close foo::<i32>(int_of_const(typeid(N)));
    p.first
}

unsafe fn outer_first<const N: usize>(o: Outer<N>) -> i32
//@ req true;
//@ ens foo::<i32>(int_of_const(typeid(N)));
{
    //@ close foo::<i32>(int_of_const(typeid(N)));
    o.inner.first
}

// A use site combining a lifetime parameter with a const parameter.
unsafe fn with_lifetime_len<'a, const N: usize>(w: *const WithLifetime<'a, i32, N>)
//@ req true;
//@ ens foo::<i32>(int_of_const(typeid(N)));
{
    //@ close foo::<i32>(int_of_const(typeid(N)));
}

unsafe fn main()
//@ req true;
//@ ens true;
{
    let b = Buf::<4> { len: 3 };
    buf_len::<4>(b);
    //@ open foo(?n1);
    //@ assert n1 == 4;

    let p = Pair::<i32, 7, usize> { first: 1, second: 0 };
    pair_first::<7>(p);
    //@ open foo(?n2);
    //@ assert n2 == 7;

    let c = Choice::<i32, 3>::Right(0);

    let o = Outer::<11> { inner: Pair::<i32, 11, usize> { first: 2, second: 0 } };
    outer_first::<11>(o);
    //@ open foo(?n3);
    //@ assert n3 == 11;
}
