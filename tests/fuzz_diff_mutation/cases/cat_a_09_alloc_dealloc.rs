// verifast_options{ignore_unwind_paths}
use std::alloc::{alloc, dealloc, Layout, handle_alloc_error};

pub unsafe fn test_alloc_dealloc() -> u8
//@ req true;
//@ ens result == 42;
{
    let layout = Layout::new::<u8>();
    let p = alloc(layout);
    if p.is_null() {
        handle_alloc_error(layout);
    }
    *p = 42;
    let v = *p;
    dealloc(p, layout);
    v
}
fn main() {}
