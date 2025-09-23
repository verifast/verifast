// verifast_options{ignore_unwind_paths}

use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

unsafe fn assert(b: bool)
//@ req b;
//@ ens true;
{}

struct Account {
    balance: i32
}

/*@

pred Account(account: *Account; balance: i32) =
    alloc_block_Account(account) &*&
    (*account).balance |-> balance;

@*/

impl Account {

    unsafe fn new() -> *mut Account
    //@ req true;
    //@ ens Account(result, 0);
    {
        let account = alloc(Layout::new::<Account>()) as *mut Account;
        if account.is_null() {
            handle_alloc_error(Layout::new::<Account>());
        }
        (*account).balance = 0;
        return account;
    }

    unsafe fn get_balance(account: *mut Account) -> i32
    //@ req Account(account, ?balance);
    //@ ens Account(account, balance) &*& result == balance;
    {
        return (*account).balance;
    }

    unsafe fn deposit(account: *mut Account, amount: i32)
    //@ req Account(account, ?balance) &*& 0 <= amount &*& balance + amount <= 2000000000;
    //@ ens Account(account, balance + amount);
    {
        (*account).balance += amount;
    }

    unsafe fn dispose(account: *mut Account)
    //@ req Account(account, _);
    //@ ens true;
    {
        dealloc(account as *mut u8, Layout::new::<Account>());
    }

}

fn main() {
    unsafe {
        let account = Account::new();
        Account::deposit(account, 1000);
        assert(Account::get_balance(account) == 1000);
        Account::dispose(account);
    }
}
