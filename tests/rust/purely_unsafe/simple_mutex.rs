/*@

pred_ctor SimpleMutex_inv(mutex: platform::threading::Mutex, inv_: pred())() =
    [1/2]platform::threading::Mutex_state(mutex, ?state) &*&
    match state {
        none() => inv_() &*& [1/2]platform::threading::Mutex_state(mutex, state),
        some(owner) => true
    };

pred SimpleMutex(mutex: platform::threading::Mutex, inv_: pred();) =
    platform::threading::Mutex(mutex) &*&
    atomic_space(MaskTop, SimpleMutex_inv(mutex, inv_));

pred SimpleMutex_held(mutex: platform::threading::Mutex, inv_: pred(), owner: usize) =
    [_]platform::threading::Mutex(mutex) &*&
    [_]atomic_space(MaskTop, SimpleMutex_inv(mutex, inv_)) &*&
    [1/2]platform::threading::Mutex_state(mutex, some(owner));

@*/

pub unsafe fn SimpleMutex_new() -> platform::threading::Mutex
//@ req exists::<pred()>(?inv_) &*& inv_();
//@ ens [_]SimpleMutex(result, inv_);
{
    //@ open exists(_);
    let mutex = platform::threading::Mutex::new();
    //@ close SimpleMutex_inv(mutex, inv_)();
    //@ create_atomic_space(MaskTop, SimpleMutex_inv(mutex, inv_));
    //@ leak SimpleMutex(mutex, inv_);
    mutex
}

/*@

pred_ctor SimpleMutex_acquire_pre(mutex: platform::threading::Mutex, inv_: pred())() =
    [_]atomic_space(MaskTop, SimpleMutex_inv(mutex, inv_));
pred_ctor SimpleMutex_acquire_post(mutex: platform::threading::Mutex, inv_: pred(), acquirer: i32)() =
    [1/2]platform::threading::Mutex_state(mutex, some(acquirer)) &*& inv_();

@*/

pub unsafe fn SimpleMutex_acquire(mutex: platform::threading::Mutex)
//@ req [_]SimpleMutex(mutex, ?inv_);
//@ ens SimpleMutex_held(mutex, inv_, currentThread) &*& inv_();
{
    //@ let acquirer = currentThread;
    /*@
    produce_lem_ptr_chunk platform::threading::Mutex_acquire_ghop(mutex, currentThread, SimpleMutex_acquire_pre(mutex, inv_), SimpleMutex_acquire_post(mutex, inv_, currentThread))() {
        assert platform::threading::is_Mutex_acquire_op(?op, _, _, _, _);
        open SimpleMutex_acquire_pre(mutex, inv_)();
        open_atomic_space(MaskTop, SimpleMutex_inv(mutex, inv_));
        open SimpleMutex_inv(mutex, inv_)();
        op();
        close SimpleMutex_inv(mutex, inv_)();
        close_atomic_space(MaskTop);
        close SimpleMutex_acquire_post(mutex, inv_, acquirer)();
    };
    @*/
    //@ close SimpleMutex_acquire_pre(mutex, inv_)();
    mutex.acquire();
    //@ open SimpleMutex_acquire_post(mutex, inv_, acquirer)();
    //@ close SimpleMutex_held(mutex, inv_, currentThread);
}

/*@

pred_ctor SimpleMutex_release_pre(mutex: platform::threading::Mutex, inv_: pred(), releaser: i32)() =
    [_]atomic_space(MaskTop, SimpleMutex_inv(mutex, inv_)) &*&
    [1/2]platform::threading::Mutex_state(mutex, some(releaser)) &*& inv_();
pred_ctor SimpleMutex_release_post(mutex: platform::threading::Mutex, inv_: pred(), acquirer: i32)() =
    true;
pred True() = true;

@*/

pub unsafe fn SimpleMutex_release(mutex: platform::threading::Mutex)
//@ req SimpleMutex_held(mutex, ?inv_, currentThread) &*& inv_();
//@ ens true;
{
    //@ open SimpleMutex_held(mutex, inv_, currentThread);
    //@ let releaser = currentThread;
    /*@
    produce_lem_ptr_chunk platform::threading::Mutex_release_ghop(mutex, currentThread, SimpleMutex_release_pre(mutex, inv_, releaser), True)() {
        assert platform::threading::is_Mutex_release_op(?op, _, _, _, _);
        open SimpleMutex_release_pre(mutex, inv_, releaser)();
        open_atomic_space(MaskTop, SimpleMutex_inv(mutex, inv_));
        open SimpleMutex_inv(mutex, inv_)();
        op();
        close SimpleMutex_inv(mutex, inv_)();
        close_atomic_space(MaskTop);
        close True();
    };
    @*/
    //@ close SimpleMutex_release_pre(mutex, inv_, releaser)();
    mutex.release();
    //@ open True();
}
