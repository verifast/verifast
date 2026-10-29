pub unsafe fn new(b: bool)
//@ req thread_token(?tid) &*& tid == currentThread;
//@ ens thread_token(tid);
//@ on_unwind_ens thread_token(tid);
{
    if b {
        panic!("ManuallyDrop CFG regression");
    }
}

pub unsafe fn ordinary_caller(b: bool)
//@ req thread_token(?tid) &*& tid == currentThread;
//@ ens thread_token(tid);
//@ on_unwind_ens thread_token(tid);
{
    new(b);
}

pub unsafe fn shared_cleanup<T>(t: T, b: bool)
//@ req thread_token(?tid) &*& tid == currentThread;
//@ ens thread_token(tid);
//@ on_unwind_ens thread_token(tid);
{
    let _ = std::mem::ManuallyDrop::new(t);
    new(b);
}

// Positive control with the same normal-first shape as the false-unwind test.
pub unsafe fn normal_first_cleanup<T>(t: T, b: bool)
//@ req thread_token(?tid) &*& tid == currentThread;
//@ ens thread_token(tid);
//@ on_unwind_ens thread_token(tid);
{
    let _ = std::mem::ManuallyDrop::new(t);
    if b {
    } else {
        new(true)
    }
}
