use std::boxed::Box;
use std::option::Option;
fn foo(x: Box<i32>) -> i32 { *x }
fn bar(x: i32) -> i32 { foo(Box::new(x)) }
fn baz(x: Option<i32>) -> i32 { x.map_or_else(|| 42, |v| v / 2) }
