class Purse {
    short balance;
}

class Program {
    Purse p1, p2;
    
    void deposit(Purse p, short amount)
        //@ requires Purse_balance(p, ?b);
        //@ ensures Purse_balance(p, (short)(b + amount));
    {
        p.balance += amount;
    }
    
    Program()
        //@ requires true;
        //@ ensures true;
    {
        p1 = new Purse();
        deposit(p1, (short)100);
        p2 = new Purse();
        deposit(p2, (short)50);
        
        short b1 = p1.balance;
        short b2 = p2.balance;
        assert b1 == 100 && b2 == 50;
    }
}