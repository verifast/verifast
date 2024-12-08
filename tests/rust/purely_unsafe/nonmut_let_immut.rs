unsafe fn mutate(p: *const i32)
//@ req *p |-> _;
//@ ens *p |-> 42;
{
    *(p as *mut i32) = 42;
}

fn foo()
//@ req true;
//@ ens true;
{
    let mut z = 24;
    unsafe { mutate(&raw const z); } // No UB

    let x = 24;
    unsafe { mutate(&raw const x); } //~should_fail // UB!
}
