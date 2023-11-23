unsafe fn assert(b: bool)
//@ req b;
//@ ens true;
{}

struct Account {
    balance: i32
}

/*@

pred Account(account: *Account; balance: i32) =
    alloc_block(account, std::mem::size_of::<Account>()) &*& struct_Account_padding(account) &*&
    (*account).balance |-> balance;

@*/

unsafe fn create_account() -> *mut Account
//@ req true;
//@ ens Account(result, 0);
{
    let account = std::alloc::alloc(std::alloc::Layout::new::<Account>()) as *mut Account;
    if account.is_null() {
        std::alloc::handle_alloc_error(std::alloc::Layout::new::<Account>());
    }
    //@ close_struct(account);
    (*account).balance = 0;
    return account;
}

unsafe fn account_get_balance(account: *mut Account) -> i32
//@ req Account(account, ?balance);
//@ ens Account(account, balance) &*& result == balance;
{
    return (*account).balance;
}

unsafe fn account_deposit(account: *mut Account, amount: i32)
//@ req Account(account, ?balance) &*& 0 <= amount &*& balance + amount <= 2000000000;
//@ ens Account(account, balance + amount);
{
    (*account).balance += amount;
}

unsafe fn account_dispose(account: *mut Account)
//@ req Account(account, _);
//@ ens true;
{
    //@ open_struct(account);
    std::alloc::dealloc(account as *mut u8, std::alloc::Layout::new::<Account>());
}

fn main() {
    unsafe {
        let account = create_account();
        account_deposit(account, 1000);
        assert(account_get_balance(account) == 1000);
        account_dispose(account);
    }
}
