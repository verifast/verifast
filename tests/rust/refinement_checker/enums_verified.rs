fn foo(x: Option<i32>) -> Option<i32>
{
    match x {
        None => {
            let r = None;
            r
        }
        Some(y) => {
            let r = Some(y);
            r
        }
    }
}
