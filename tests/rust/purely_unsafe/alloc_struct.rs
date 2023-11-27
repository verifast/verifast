struct Node {
    value: u8,
}

fn main() {
    unsafe {
        let layout = std::alloc::Layout::new::<Node>();
        let p = std::alloc::alloc(layout) as *mut Node;
        if p.is_null() {
            std::alloc::handle_alloc_error(layout);
        }
        //@ close_struct(p);
        (*p).value = 42;
        if (*p).value != 42 {
            std::alloc::dealloc(p as *mut u8, layout);
            std::alloc::dealloc(p as *mut u8, layout);
        }
        //@ open_struct(p);
        std::alloc::dealloc(p as *mut u8, layout);
    }
}
