// verifast_options{extern_spec:platform=../../unverified/platform/spec/lib.rsspec extern_spec:simple_mutex=../simple_mutex/spec/lib.rsspec}

use simple_mutex::Mutex;
//@ use simple_mutex::Mutex;

struct Accounts {
    mutex: simple_mutex::Mutex,
    balance1: i32,
    balance2: i32,
}

/*@

pred_ctor Accounts_inv(accounts: *mut Accounts)() =
    [1/2](*accounts).balance1 |-> ?balance1 &*&
    [1/2](*accounts).balance2 |-> ?balance2 &*&
    balance1 + balance2 == 2000;

pred transfer_pre(accounts: *mut Accounts;) =
    (*accounts).mutex |-> ?mutex &*&
    [1/2](*accounts).balance1 |-> 2000 &*&
    [1/2](*accounts).balance2 |-> 0 &*&
    [1/2]Mutex(mutex, Accounts_inv(accounts));

@*/

unsafe fn transfer(accounts: *mut Accounts)
//@ req transfer_pre(accounts);
//@ ens true;
{
    simple_mutex::Mutex::acquire((*accounts).mutex);
    //@ open Accounts_inv(accounts)();
    (*accounts).balance1 -= 1000;
    (*accounts).balance2 += 1000;
    //@ close Accounts_inv(accounts)();
    simple_mutex::Mutex::release((*accounts).mutex);
    //@ leak (*accounts).mutex |-> _;
    //@ leak [1/2](*accounts).balance1 |-> _;
    //@ leak [1/2](*accounts).balance2 |-> _;
    //@ leak [1/2]Mutex(_, _);
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
        std::ptr::write(&raw mut (*accounts).balance1, 2000);
        std::ptr::write(&raw mut (*accounts).balance2, 0);
        //@ close Accounts_inv(accounts)();
        //@ close exists(Accounts_inv(accounts));
        let mutex = Mutex::new();
        std::ptr::write(&raw mut (*accounts).mutex, mutex);
        //@ produce_fn_ptr_chunk platform::threading::thread_run<*mut Accounts>(transfer)(transfer_pre)(data) { call(); }
        platform::threading::fork(transfer, accounts);
        Mutex::acquire(mutex);
        //@ open Accounts_inv(accounts)();
        let balance1 = (*accounts).balance1;
        let balance2 = (*accounts).balance2;
        //@ close Accounts_inv(accounts)();
        assert(balance1 + balance2 == 2000);
        Mutex::release(mutex);
        std::process::exit(0);
    }
}
