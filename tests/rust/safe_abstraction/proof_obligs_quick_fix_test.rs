struct Foo {
    x: i32,
    y: i32,
}

/*@

pred <Foo>.own(t, foo) = t == default_tid;

pred <Foo>.share(k, t, l) = t == default_tid;

@*/
