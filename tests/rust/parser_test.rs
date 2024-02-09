// Tests for the Rust parser
struct Foo {
    v: i32,
}

unsafe fn f(p: *mut Foo)
//@ req [?q](*p).v |-> ?v;
//@ ens [q](*p).v |-> v;
{
}
