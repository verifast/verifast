use std::result::Result;

fn foo(r: Result<i32, *mut u8>) -> Result<bool, *mut u8> {
    match r {
        Ok(x) => Ok(x < 0),
        Err(e) => Err(e)
    }
}
