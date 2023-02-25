fn main()
{
    unsafe {
        let layout = std::alloc::Layout::new::<u8>();
        let p = std::alloc::alloc(layout);
        if p.is_null() {
            std::alloc::handle_alloc_error(layout);
        }
        *p = 42;
        if *p != 42 {
            std::alloc::dealloc(p, layout);
            std::alloc::dealloc(p, layout);
        }
        std::alloc::dealloc(p, layout);
    }
}
