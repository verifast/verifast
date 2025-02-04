unsafe fn call_fnonce<F: FnOnce()>(f: F)
//@ req thread_token(?t) &*& <F>.own(t, f);
//@ ens thread_token(t);
//@ on_unwind_ens thread_token(t);
{
    //@ close_tuple_0_own(t);
    f();
    //@ open_tuple_0_own(t);
}
