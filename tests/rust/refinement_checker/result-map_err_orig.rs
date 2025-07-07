use std::result::Result;

fn foo(r: Result<*mut u8, i32>) -> Result<*mut u8, bool> {
    r.map_err(|x| x < 0)
}
