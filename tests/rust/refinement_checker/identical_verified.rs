use std::boxed::Box; // This comment is ignored
use std::option::Option;
fn foo(x: Box<i32>) -> i32 { *x }
fn bar(x: i32) -> i32
{
    let b = Box::new(x);
    let r = foo(b);
    r
} /* It's okay to have extra comments /* and even nested ones */ */
fn baz(x: Option<i32>) -> i32 { x.map_or_else(|| 42, |v| v / 2) }
