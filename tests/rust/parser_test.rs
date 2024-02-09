// Tests for the Rust parser
mod foo {
    struct Foo {
        v: i32,
    }

    //@ pred foo::Foo_own(t: thread_id_t, v: i32) = true;
}

/*@
lem foo::Foo_dummy(p: *foo::Foo)
req [?q](*p).v |-> ?v &*& foo::Foo_own(?t, v);
ens [q](*p).v |-> v &*& foo::Foo_own(t, v);
{}
@*/
