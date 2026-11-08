// verifast_options{ignore_unwind_paths}
use std::alloc::{alloc, dealloc, Layout, handle_alloc_error};

pub unsafe fn bad_uaf() -> u8
//@ req true;
//@ ens true;
{
    let layout = Layout::new::<u8>();
    let p = alloc(layout);
    if p.is_null() {
        handle_alloc_error(layout);
    }
    *p = 77;
    dealloc(p, layout);
    *p
}
fn main() {}
