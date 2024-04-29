pub mod ptr {
    pub struct NonNull<T> {
        pointer: *const T,
    }

    impl<T> NonNull<T> {
        pub fn from<'a>(reference: &'a mut T) -> Self {
            NonNull {
                pointer: reference as *mut T,
            }
        }

        pub unsafe fn new_unchecked(ptr: *mut T) -> Self {
            NonNull { pointer: ptr }
        }

        pub unsafe fn as_ref<'a>(&'a self) -> &'a T {
            &*self.pointer
        }

        pub fn as_ptr(self) -> *mut T {
            self.pointer as *mut T
        }
    }

    impl<T> Copy for NonNull<T> {}
    impl<T> Clone for NonNull<T> {
        fn clone<'a>(&'a self) -> Self {
            *self
        }
    }
}
