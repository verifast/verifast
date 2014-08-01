// An extremely flexible Person class, where subclasses are not required to store the spouse in the spouse field.
// Two layers of specification seem to be required: an inner layer that deals with storage of the spouse field, and
// an outer layer that encapsulates the bidirectionality of the association.

class Person {

    private Person spouse;

    /*@
    
    protected predicate ticket(Person spouse) = [1/2]this.spouse |-> spouse &*& spouse != null;
    protected predicate valid0(Person spouse) = [1/2]this.spouse |-> spouse &*& spouse == null ? [1/2]this.spouse |-> null : emp;
    
    public predicate valid(Person spouse) = this.valid0(spouse) &*& spouse != null ? spouse.ticket(this) : emp;
    
    @*/
    
    protected Person getSpouse0()
        //@ requires valid0(?s);
        //@ ensures valid0(s) &*& result == s;
    {
        //@ open valid0(s);
        Person result = spouse;
        //@ close valid0(s);
        return result;
    }
    
    protected void setSpouse0(Person other)
        //@ requires valid0(null) &*& other != null;
        //@ ensures valid0(other) &*& ticket(other);
    {
        //@ open valid0(null);
        spouse = other;
        //@ close valid0(other);
        //@ close ticket(other);
    }
    
    protected void clearSpouse0()
        //@ requires valid0(?other) &*& ticket(_);
        //@ ensures valid0(null) &*& other != null;
    {
        //@ open valid0(other);
        //@ open ticket(_);
        spouse = null;
        //@ close valid0(null);
    }
    
    protected void setSpouse(Person other)
        //@ requires valid(null) &*& other.ticket(this);
        //@ ensures valid(other) &*& this.ticket(other);
    {
        //@ open valid(null);
        setSpouse0(other);
        //@ close valid(other);
    }
    
    protected void clearSpouse()
        //@ requires valid(?s) &*& this.ticket(_);
        //@ ensures valid(null) &*& s.ticket(this);
    {
        //@ open valid(s);
        clearSpouse0();
        //@ close valid(null);
    }
    
    /*@
    
    protected lemma void ticketLemma0()
        requires valid0(?s) &*& ticket(?s0);
        ensures valid0(s) &*& ticket(s0) &*& s == s0;
    {
        open valid0(s);
        open ticket(s0);
        close valid0(s);
        close ticket(s0);
    }
    
    @*/
    
    protected /*lemma*/ void ticketLemma()
        //@ requires valid(?s) &*& this.ticket(?s0);
        //@ ensures valid(s) &*& this.ticket(s0) &*& s == s0;
    {
        //@ open valid(s);
        //@ ticketLemma0();
        //@ close valid(s);
    }
    
    public /*lemma*/ void symmetryLemma()
        //@ requires valid(?s) &*& s.valid(?ss);
        //@ ensures valid(s) &*& s.valid(ss) &*& ss == this;
    {
        //@ open valid(s);
        Person spouse = getSpouse0();
        spouse.ticketLemma();
        //@ close valid(s);
    }

    protected Person()
        //@ requires true;
        //@ ensures valid0(null);
    {
        //@ close valid0(null);
    }
    
    /*@
    
    protected lemma void initLemma()
        requires this.valid0(null);
        ensures valid(null);
    {
        close valid(null);
    }
    
    @*/
    
    public static Person create()
        //@ requires true;
        //@ ensures result.valid(null);
    {
        Person p = new Person();
        //@ p.initLemma();
        return p;
    }
    
    public Person getSpouse()
        //@ requires valid(?s);
        //@ ensures valid(s) &*& result == s;
    {
        //@ open valid(s);
        return getSpouse0();
        //@ close valid(s);
    }
    
    void marry(Person other)
        //@ requires valid(null) &*& other.valid(null);
        //@ ensures valid(other) &*& other.valid(this);
    {
        //@ open valid(null);
        setSpouse0(other);
        other.setSpouse(this);
        //@ close valid(other);
    }
    
    void divorce()
        //@ requires valid(?other) &*& other.valid(this);
        //@ ensures valid(null) &*& other.valid(null);
    {
        //@ open valid(other);
        Person spouse = getSpouse0();
        spouse.clearSpouse();
        clearSpouse0();
        //@ close valid(null);
    }

}

class Program {

    public static void main(String[] args)
        //@ requires true;
        //@ ensures true;
    {
        Person a = Person.create();
        Person b = Person.create();
        a.marry(b);
        b.divorce();
    }

}