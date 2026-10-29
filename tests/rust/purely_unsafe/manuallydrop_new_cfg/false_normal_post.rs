pub unsafe fn forget_false_normal_post<T>(t: T)
//@ req thread_token(?tid) &*& tid == currentThread;
//@ ens false; //~should_fail
//@ on_unwind_ens false;
{
    let _ = std::mem::ManuallyDrop::new(t);
}
