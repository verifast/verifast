class Account {

    int balance;
    
    //@ predicate valid(int balance) = this.balance |-> balance;
    
    Account()
        //@ requires true;
        //@ ensures valid(0);
    {
        //@ close valid(0);
    }
    
    int getBalance()
        //@ requires valid(?b);
        //@ ensures valid(b) &*& result == b;
    {
        //@ open valid(b);
        return balance;
        //@ close valid(b);
    }
    
    void deposit(int amount)
        //@ requires valid(?b);
        //@ ensures valid(b + amount);
    {
        //@ open valid(b);
        balance += amount;
        //@ close valid(_);
    }
    
    void transferTo(Account target, int amount)
        //@ requires this.valid(?b) &*& target.valid(?bt);
        //@ ensures this.valid(b - amount) &*& target.valid(bt + amount);
    {
        deposit(-amount);
        target.deposit(amount);
    }

}

class Program {

    public static void main(String[] args)
        //@ requires true;
        //@ ensures true;
    {
        Account a = new Account();
        a.deposit(1000);
        
        Account b = new Account();
        b.deposit(2000);
        
        a.transferTo(b, 500);
        
        int ba = a.getBalance();
        int bb = b.getBalance();
        assert ba == 500 && bb == 2500;
    }

}
