use std::ptr::NonNull;
unsafe fn bar(mut x: NonNull<i32>, y: NonNull<i32>) {
    let mut z = NonNull::<i32>::dangling();
    x = y;
    loop {
        x.as_mut();
    }
}
