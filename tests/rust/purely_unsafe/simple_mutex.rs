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

unsafe fn SimpleMutex_new() -> platform::threading::Mutex
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

unsafe fn SimpleMutex_acquire(mutex: platform::threading::Mutex)
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

unsafe fn SimpleMutex_release(mutex: platform::threading::Mutex)
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

struct Accounts {
    mutex: platform::threading::Mutex,
    balance1: i32,
    balance2: i32,
}

/*@

pred_ctor Accounts_inv(accounts: *mut Accounts)() =
    [1/2](*accounts).balance1 |-> ?balance1 &*&
    [1/2](*accounts).balance2 |-> ?balance2 &*&
    balance1 + balance2 == 2000;

pred transfer_pre(data: *mut u8;) = transfer_pre0(data as *mut Accounts);

pred transfer_pre0(accounts: *mut Accounts;) =
    (*accounts).mutex |-> ?mutex &*&
    [1/2](*accounts).balance1 |-> 2000 &*&
    [1/2](*accounts).balance2 |-> 0 &*&
    [_]SimpleMutex(mutex, Accounts_inv(accounts));

@*/

unsafe fn transfer(data: *mut u8)
//@ req transfer_pre(data);
//@ ens true;
{
    //@ open transfer_pre(data);
    let accounts = data as *mut Accounts;
    //@ open transfer_pre0(accounts);
    SimpleMutex_acquire((*accounts).mutex);
    //@ open Accounts_inv(accounts)();
    (*accounts).balance1 -= 1000;
    (*accounts).balance2 += 1000;
    //@ close Accounts_inv(accounts)();
    SimpleMutex_release((*accounts).mutex);
    //@ leak (*accounts).mutex |-> _;
    //@ leak [1/2](*accounts).balance1 |-> _;
    //@ leak [1/2](*accounts).balance2 |-> _;
}

unsafe fn assert(b: bool)
//@ req b;
//@ ens true;
{
    if !b { //~allow_dead_code
        let p = std::ptr::null_mut(); //~allow_dead_code
        *p = 42; //~allow_dead_code
    }
}

fn main() {
    unsafe {
        let layout = std::alloc::Layout::new::<Accounts>();
        let accounts = std::alloc::alloc(layout) as *mut Accounts;
        if accounts.is_null() {
            std::alloc::handle_alloc_error(layout);
        }
        //@ close_struct(accounts);
        std::ptr::write(std::ptr::addr_of_mut!((*accounts).balance1), 2000);
        std::ptr::write(std::ptr::addr_of_mut!((*accounts).balance2), 0);
        //@ close Accounts_inv(accounts)();
        //@ close exists(Accounts_inv(accounts));
        let mutex = SimpleMutex_new();
        std::ptr::write(std::ptr::addr_of_mut!((*accounts).mutex), mutex);
        //@ produce_fn_ptr_chunk platform::threading::thread_run(transfer)(transfer_pre)(data) { call(); }
        platform::threading::fork(transfer, accounts as *mut u8);
        SimpleMutex_acquire(mutex);
        //@ open Accounts_inv(accounts)();
        let balance1 = (*accounts).balance1;
        let balance2 = (*accounts).balance2;
        //@ close Accounts_inv(accounts)();
        assert(balance1 + balance2 == 2000);
        SimpleMutex_release(mutex);
        std::process::exit(0);
    }
}
