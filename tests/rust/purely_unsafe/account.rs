unsafe fn assert(b: bool)
//@ requires b;
//@ ensures true;
{}

struct Account {
    balance: i32
}

/*@

predicate Account(struct Account *account; int balance) =
    malloc_block(account, sizeof(struct Account)) &*& struct_Account_padding(account) &*&
    account->balance |-> balance;

@*/

unsafe fn create_account() -> *mut Account
//@ requires true;
//@ ensures Account(result, 0);
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
//@ requires Account(account, ?balance);
//@ ensures Account(account, balance) &*& result == balance;
{
    return (*account).balance;
}

unsafe fn account_deposit(account: *mut Account, amount: i32)
//@ requires Account(account, ?balance) &*& 0 <= amount &*& balance + amount <= 2000000000;
//@ ensures Account(account, balance + amount);
{
    (*account).balance += amount;
}

unsafe fn account_dispose(account: *mut Account)
//@ requires Account(account, _);
//@ ensures true;
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
