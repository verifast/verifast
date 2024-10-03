// verifast_options{extern:../unverified/platform}

mod simple_mutex;

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
    [_]simple_mutex::SimpleMutex(mutex, Accounts_inv(accounts));

@*/

unsafe fn transfer(data: *mut u8)
//@ req transfer_pre(data);
//@ ens true;
{
    //@ open transfer_pre(data);
    let accounts = data as *mut Accounts;
    //@ open transfer_pre0(accounts);
    simple_mutex::SimpleMutex_acquire((*accounts).mutex);
    //@ open Accounts_inv(accounts)();
    (*accounts).balance1 -= 1000;
    (*accounts).balance2 += 1000;
    //@ close Accounts_inv(accounts)();
    simple_mutex::SimpleMutex_release((*accounts).mutex);
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
        let mutex = simple_mutex::SimpleMutex_new();
        std::ptr::write(std::ptr::addr_of_mut!((*accounts).mutex), mutex);
        //@ produce_fn_ptr_chunk platform::threading::thread_run(transfer)(transfer_pre)(data) { call(); }
        platform::threading::fork(transfer, accounts as *mut u8);
        simple_mutex::SimpleMutex_acquire(mutex);
        //@ open Accounts_inv(accounts)();
        let balance1 = (*accounts).balance1;
        let balance2 = (*accounts).balance2;
        //@ close Accounts_inv(accounts)();
        assert(balance1 + balance2 == 2000);
        simple_mutex::SimpleMutex_release(mutex);
        std::process::exit(0);
    }
}
