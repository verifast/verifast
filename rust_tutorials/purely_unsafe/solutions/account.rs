// verifast_options{ignore_unwind_paths}
use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Account {
    balance: i32,
}

impl Account {

    unsafe fn create() -> *mut Account
    //@ req true;
    //@ ens Account_balance(result, 0) &*& alloc_block_Account(result);
    {
        let my_account = alloc(Layout::new::<Account>()) as *mut Account;
        if my_account.is_null() {
            handle_alloc_error(Layout::new::<Account>());
        }
        (*my_account).balance = 0;
        my_account
    }

    unsafe fn set_balance(my_account: *mut Account, new_balance: i32)
    //@ req Account_balance(my_account, _);
    //@ ens Account_balance(my_account, new_balance);
    {
        (*my_account).balance = new_balance;
    }

    unsafe fn dispose(my_account: *mut Account)
    //@ req Account_balance(my_account, _) &*& alloc_block_Account(my_account);
    //@ ens true;
    {
        dealloc(my_account as *mut u8, Layout::new::<Account>());
    }

}

fn main()
//@ req true;
//@ ens true;
{
    unsafe {
        let my_account = Account::create();
        Account::set_balance(my_account, 5);
        Account::dispose(my_account);
    }
}
