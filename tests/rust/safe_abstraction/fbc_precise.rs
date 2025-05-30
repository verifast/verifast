#![feature(negative_impls)]
struct Foo();
//@ pred <Foo>.own(t, f;) = true;

impl Drop for Foo {
    fn drop(&mut self) {}
}
