fn print(x: i32) -> i32 { print(x) }
fn foo(mut x: i32)
{
    loop {
        let w = x;
        x = print(w);
    }
}
