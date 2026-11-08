// verifast_options{skip_specless_fns}
pub struct Point {
    pub x: i32,
    pub y: i32,
}

pub unsafe fn test_struct_field_ptr() -> i32
//@ req true;
//@ ens result == 99;
{
    let mut pt = Point { x: 10, y: 20 };
    let p = &raw mut pt;
    (*p).x = 99;
    (*p).x
}
fn main() {}
