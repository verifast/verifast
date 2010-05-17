public class Person {

    private Person spouse;

    /*@
    
    protected predicate ticket(Person spouse) = [1/2]this.spouse |-> spouse &*& spouse != null;
    
    public predicate valid(Person spouse) = [1/2]this.spouse |-> spouse &*& spouse == null ? [1/2]this.spouse |-> null : spouse.ticket(this);
    
    @*/
    
    protected void setSpouse(Person other)
        //@ requires valid(null) &*& other.ticket(this);
        //@ ensures valid(other) &*& ticket(other);
    {
        //@ open valid(null);
        spouse = other;
        //@ close valid(other);
        //@ close ticket(other);
    }
    
    protected void clearSpouse()
        //@ requires valid(?s) &*& ticket(_);
        //@ ensures valid(null) &*& s.ticket(this);
    {
        //@ open valid(s);
        //@ open ticket(_);
        spouse = null;
        //@ close valid(null);
    }
    
    protected /*lemma*/ void spouse_ticket_lemma()
        //@ requires valid(?s) &*& ticket(?s0);
        //@ ensures valid(s) &*& ticket(s0) &*& s == s0;
    {
        //@ open valid(s);
        //@ open ticket(s0);
        //@ close valid(s);
        //@ close ticket(s0);
    }
    
    public /*lemma*/ void spouse_symm()
        //@ requires valid(?s) &*& s.valid(?ss);
        //@ ensures valid(s) &*& s.valid(ss) &*& ss == this;
    {
        //@ open valid(s);
        spouse.spouse_ticket_lemma();
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
        Person result = spouse;
        //@ close valid(s);
        return result;
    }
    
    void marry(Person other)
        //@ requires valid(null) &*& other.valid(null);
        //@ ensures valid(other) &*& other.valid(this);
    {
        //@ open valid(null);
        spouse = other;
        //@ close ticket(other);
        other.setSpouse(this);
        //@ close valid(other);
    }
    
    void divorce()
        //@ requires valid(?other) &*& other.valid(this);
        //@ ensures valid(null) &*& other.valid(null);
    {
        //@ open valid(other);
        spouse.clearSpouse();
        //@ open ticket(other);
        spouse = null;
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