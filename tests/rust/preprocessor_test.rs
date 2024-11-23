fn foo(x: i32) -> i32
//@ req true;
//@ ens result == 42;
{
    //@ assume(x == 42);
    x
}

fn bar(x: i32) -> i32
//@ req true;
//@ ens result == 43; //~should_fail
{
    //@ assume(x == 42);
    x
}
