use std::boxed::Box;
struct Option<T> { marker: std::marker::PhantomData<T> }
impl<T> Option<T> { fn map_or_else<U, D: FnOnce() -> U, F: FnOnce(T) -> U>(self, d: D, f: F) -> U { d() } }
fn foo(x: Box<i32>) -> i32 { *x }
fn bar(x: i32) -> i32
{
    let b = Box::new(x);
    let r = foo(b);
    r
}
fn baz(x: Option<i32>) -> i32 { x.map_or_else(|| 42, |v| v / 2) }
