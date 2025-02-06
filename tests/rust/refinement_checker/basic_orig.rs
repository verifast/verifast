unsafe fn foo(x: i32, y: i32, z: i32) -> i32 {
    x.unchecked_sub(y.unchecked_sub(z))
}
