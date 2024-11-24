use std::alloc::{alloc, Layout, handle_alloc_error, dealloc};

unsafe fn assert(b: bool)
//@ req b;
//@ ens true;
{}

struct Account {
    balance: i32
}

impl Account {

    unsafe fn new() -> Account
    //@ req true;
    //@ ens result == Account { balance: 0 };
    {
        return Account { balance: 0 };
    }
    
    unsafe fn init(account_ptr: *mut Account)
    //@ req *account_ptr |-> _;
    //@ ens *account_ptr |-> Account { balance: 0 };
    {
        (*account_ptr).balance = 0;
    }

    unsafe fn get_balance(account_ptr: *mut Account) -> i32
    //@ req *account_ptr |-> ?account;
    //@ ens *account_ptr |-> account &*& result == account.balance;
    {
        return (*account_ptr).balance;
    }

    unsafe fn deposit(account_ptr: *mut Account, amount: i32)
    //@ req *account_ptr |-> ?account &*& 0 <= amount &*& account.balance + amount <= 2000000000;
    //@ ens *account_ptr |-> Account { balance: account.balance + amount };
    {
        let balance = (*account_ptr).balance;
        //@ produce_limits(balance);
        (*account_ptr).balance = balance + amount;
    }
    
    unsafe fn drop_in_place(account_ptr: *mut Account)
    //@ req *account_ptr |-> ?_;
    //@ ens *account_ptr |-> _;
    {}

}

fn main1() {
    unsafe {
        let mut account = Account::new();
        Account::deposit(&raw mut account, 1000);
        assert(Account::get_balance(&raw mut account) == 1000);
    }
}

fn main2() {
    unsafe {
        let account_ptr = alloc(Layout::new::<Account>()) as *mut Account;
        if account_ptr.is_null() {
            handle_alloc_error(Layout::new::<Account>());
        }
        //@ close_struct(account_ptr);
        Account::init(account_ptr);
        Account::deposit(account_ptr, 1000);
        assert(Account::get_balance(account_ptr) == 1000);
        Account::drop_in_place(account_ptr);
        //@ open_struct(account_ptr);
        dealloc(account_ptr as *mut u8, Layout::new::<Account>());
    }
}

fn main() {
    main1();
    main2();
}
