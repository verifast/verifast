unsafe fn foo(x: i32, y: i32, z: i32) -> i32
{
    let tmp = {
        let r = y.unchecked_sub(z);
        r
    };
    x.unchecked_sub(tmp)
}
