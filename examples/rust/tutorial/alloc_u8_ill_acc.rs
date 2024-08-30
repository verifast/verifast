use std::alloc::{alloc, Layout};

unsafe fn main()
//@ req true;
//@ ens true;
{
    let l = Layout::new::<u8>();
    let p = alloc(l);
    *p = 42;
}
