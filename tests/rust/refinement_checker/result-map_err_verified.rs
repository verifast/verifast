use std::result::Result;

fn foo(r: Result<*mut u8, i32>) -> Result<*mut u8, bool> {
    match r {
        Ok(x) => Ok(x),
        Err(e) => Err(e < 0)
    }
}
