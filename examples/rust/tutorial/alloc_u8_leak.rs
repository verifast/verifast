use std::alloc::{alloc, handle_alloc_error, Layout};

unsafe fn main() {
    let l = Layout::new::<u8>();
    let p = alloc(l);
    if p.is_null() { handle_alloc_error(l); }
    *p = 42;
    assert!(*p == 42);
}
