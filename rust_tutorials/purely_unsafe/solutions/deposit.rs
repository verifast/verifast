// verifast_options{disable_overflow_check}

use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};
//@ use std::alloc::{alloc_block, Layout};

struct Account {
    balance: i32,
}

impl Account {

    unsafe fn create() -> *mut Account
    //@ req true;
    //@ ens Account_balance(result, 0) &*& alloc_block(result as *u8, Layout::new::<Account>());
    {
        let my_account = alloc(Layout::new::<Account>()) as *mut Account;
        if my_account.is_null() {
            handle_alloc_error(Layout::new::<Account>());
        }
        //@ close_struct(my_account);
        (*my_account).balance = 0;
        return my_account;
    }

    unsafe fn get_balance(my_account: *mut Account) -> i32
    //@ req Account_balance(my_account, ?theBalance);
    //@ ens Account_balance(my_account, theBalance) &*& result == theBalance;
    //@ on_unwind_ens false;
    {
        return (*my_account).balance;
    }

    unsafe fn set_balance(my_account: *mut Account, newBalance: i32)
    //@ req Account_balance(my_account, _);
    //@ ens Account_balance(my_account, newBalance);
    //@ on_unwind_ens false;
    {
        (*my_account).balance = newBalance;
    }

    unsafe fn deposit(my_account: *mut Account, amount: i32)
    //@ req Account_balance(my_account, ?theBalance);
    //@ ens Account_balance(my_account, theBalance + amount);
    //@ on_unwind_ens false;
    {
        (*my_account).balance += amount;
    }

    unsafe fn dispose(my_account: *mut Account)
    //@ req Account_balance(my_account, _) &*& alloc_block(my_account as *u8, Layout::new::<Account>());
    //@ ens true;
    {
        //@ open_struct(my_account);
        dealloc(my_account as *mut u8, Layout::new::<Account>());
    }

}

fn main() {
    unsafe {
        let my_account = Account::create();
        Account::set_balance(my_account, 5);
        Account::deposit(my_account, 10);
        let b = Account::get_balance(my_account);
        if b != 15 {
            std::hint::unreachable_unchecked();
        }
        Account::dispose(my_account);
    }
}
