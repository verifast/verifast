use std::result::Result;

fn foo(r: Result<i32, *mut u8>) -> Result<bool, *mut u8> {
    r.map(|x| x < 0)
}
