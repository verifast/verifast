fn my_replace(r: &mut i32, v: i32) -> i32 {
    let r_ref = &mut *r as *mut i32; 
    *r;
    std::mem::replace(unsafe { &mut *r_ref }, v)
}
