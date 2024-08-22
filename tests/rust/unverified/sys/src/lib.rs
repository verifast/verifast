pub mod locks {
    use std::process::abort;
    pub struct Mutex {
        m: *mut u32,
    }

    impl Mutex {
        pub unsafe fn new() -> Mutex {
            abort();
        }

        pub unsafe fn lock<'a>(&'a self) {
            abort();
        }

        pub unsafe fn unlock<'a>(&'a self) {
            abort();
        }
    }
}
