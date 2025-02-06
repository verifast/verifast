unsafe fn foo(x: i32, y: i32, z: i32) -> i32
{
    let tmp = {
        let r = z.unchecked_sub(y);
        r
    };
    x.unchecked_sub(tmp)
}
