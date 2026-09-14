// Test for const generic bool support
// Previously failed with "Unsupported constant type or size"

#![no_std]
#![allow(dead_code)]

//@ pred foo<T>(x: T) = true;

unsafe fn process_bool<const B: bool>()
//@ req true;
//@ ens foo::<i32>(int_of_const(typeid(B)));
{
    //@ close foo::<i32>(int_of_const(typeid(B)));
}

unsafe fn process_i32<const N: i32>()
//@ req true;
//@ ens foo::<i32>(int_of_const(typeid(N)));
{
    //@ close foo::<i32>(int_of_const(typeid(N)));
}

unsafe fn process_i128<const N: i128>()
//@ req true;
//@ ens foo::<i128>(int_of_const(typeid(N)));
{
    //@ close foo::<i128>(int_of_const(typeid(N)));
}

unsafe fn main()
//@ req true;
//@ ens true;
{
    process_bool::<false>();
    //@ open foo(?b1);
    //@ assert b1 == false;
    
    process_bool::<true>();
    //@ open foo(?b2);
    //@ assert b2 == true;
    
    process_i32::<42>();
    //@ open foo(?n1);
    //@ assert n1 == 42;

    process_i32::<-42>();
    //@ open foo(?n2);
    //@ assert n2 == -42;

    process_i128::<12345678901234567890>();
    //@ open foo(?n3);
    //@ assert n3 == 12345678901234567890;
    
    let f = process_i128::<-12345678901234567890>();
    //@ open foo(?n4);
    //@ assert n4 == -12345678901234567890;
}
