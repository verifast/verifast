pub unsafe fn forget_from_dead_precondition<T>(t: T)
//@ req thread_token(?tid) &*& tid == currentThread &*& false;
//@ ens thread_token(tid);
//@ on_unwind_ens false;
{
    let _ = std::mem::ManuallyDrop::new(t);
}
