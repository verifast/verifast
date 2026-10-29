pub unsafe fn new(b: bool)
//@ req thread_token(?tid) &*& tid == currentThread;
//@ ens thread_token(tid);
//@ on_unwind_ens thread_token(tid);
{
    if b {
        panic!("ManuallyDrop CFG regression");
    }
}

pub unsafe fn shared_cleanup_false_unwind_post<T>(t: T, b: bool)
//@ req thread_token(?tid) &*& tid == currentThread;
//@ ens thread_token(tid);
//@ on_unwind_ens false; //~should_fail
{
    let _ = std::mem::ManuallyDrop::new(t);
    // Visit the shared normal return before the expected unwind failure.
    if b {
    } else {
        new(true)
    }
}
