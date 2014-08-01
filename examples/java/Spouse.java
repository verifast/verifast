class Person {

    protected Person spouse;

    /*@
    
    predicate valid(Person spouse) =
        [1/2]this.spouse |-> spouse &*& spouse == null ? [1/2]this.spouse |-> null : [1/2]spouse.spouse |-> this;
    
    protected lemma void spouse_symm_helper()
        requires valid(?s) &*& [1/2]this.spouse |-> ?s0;
        ensures valid(s) &*& [1/2]this.spouse |-> s0 &*& s == s0;
    {
        open valid(s);
        close valid(s);
    }
    
    @*/
    
    public /*lemma*/ void spouse_symm()
        //@ requires valid(?s) &*& s.valid(?ss);
        //@ ensures valid(s) &*& s.valid(ss) &*& ss == this;
    {
        //@ open valid(s);
        //@ spouse.spouse_symm_helper();
        //@ close valid(s);
    }

    public Person()
        //@ requires true;
        //@ ensures valid(null);
    {
        //@ close valid(null);
    }
    
    public Person getSpouse()
        //@ requires valid(?s);
        //@ ensures valid(s) &*& result == s;
    {
        //@ open valid(s);
        return spouse;
        //@ close valid(s);
    }
    
    protected void setSpouse(Person other)
        //@ requires valid(null) &*& other.spouse |-> null;
        //@ ensures valid(other) &*& [1/2]other.spouse |-> this &*& [1/2]spouse |-> other;
    {
        //@ open valid(null);
        spouse = other;
        other.spouse = this;
        //@ close valid(other);
    }
    
    protected void clearSpouse()
        //@ requires [1/2]spouse |-> ?s &*& valid(?ss) &*& [1/2]s.spouse |-> _;
        //@ ensures valid(null) &*& s.spouse |-> null &*& ss == s;
    {
        //@ open valid(ss);
        spouse.spouse = null;
        spouse = null;
        //@ close valid(null);
    }
    
    void marry(Person other)
        //@ requires valid(null) &*& other.valid(null);
        //@ ensures valid(other) &*& other.valid(this);
    {
        //@ open valid(null);
        other.setSpouse(this);
        //@ close valid(other);
    }
    
    void divorce()
        //@ requires valid(?other) &*& other.valid(?ss);
        //@ ensures valid(null) &*& other.valid(null) &*& ss == this;
    {
        //@ open valid(other);
        spouse.clearSpouse();
        //@ close valid(null);
    }

}

class Program {

    public static void main(String[] args)
        //@ requires true;
        //@ ensures true;
    {
        Person a = new Person();
        Person b = new Person();
        a.marry(b);
        b.divorce();
    }

}