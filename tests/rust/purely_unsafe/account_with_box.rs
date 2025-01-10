unsafe fn assert(b: bool)
//@ req b;
//@ ens true;
{}

struct Account {
    balance: i32
}

/*@

pred Account(account: *Account; balance: i32) =
    std::alloc::alloc_block(account as *u8, std::alloc::Layout::new_::<Account>()) &*& struct_Account_padding(account) &*&
    (*account).balance |-> balance;

pred <Account>.own(t, account) = true;

@*/

impl Account {

    unsafe fn new() -> *mut Account
    //@ req thread_token(?t);
    //@ ens thread_token(t) &*& Account(result, 0);
    {
        let account = Account { balance: 0 };
        //@ close drop_perm::<Account>(false, True, t, account);
        let result = Box::into_raw(Box::new(account));
        //@ open drop_perm(_, _, _, _);
        result
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
    //@ req thread_token(?t) &*& Account(account, ?balance);
    //@ ens thread_token(t);
    {
        //@ close_points_to(account);
        //@ assert *account |-> ?value;
        let b = Box::from_raw(account);
        //@ close Account_own(t, value);
        //@ std::boxed::Box_to_own(b);
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
