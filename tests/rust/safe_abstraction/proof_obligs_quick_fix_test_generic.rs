struct Foo<T, U> {
    x: U,
    y: T,
}

/*@

pred<T, U> <Foo<T, U>>.own(t, foo) = t == default_tid;

pred<T, U> <Foo<T, U>>.share(k, t, l) = t == default_tid;

@*/
