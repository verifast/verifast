/*@

predicate_family MapFunc(Class c)(MapFunc f, list<int> in, list<int> out, any info);

@*/

interface MapFunc {

    int apply(int x);
        //@ requires MapFunc(this.getClass())(this, ?in, ?out, ?info) &*& switch (in) { case nil: return false; case cons(h, t): return x == h; };
        //@ ensures MapFunc(this.getClass())(this, tail(in), append(out, cons(result, nil)), info);

}

/*@

predicate_family List(Class c)(List l, list<int> xs);

lemma void list_split_fractions(List l)
    requires [_]List(?c)(l, ?xs);
    ensures List(c)(l, xs) &*& List(c)(l, xs);
{
    assume(false);
}

@*/

interface List {

    boolean isEmpty();
        //@ requires List(this.getClass())(this, ?xs);
        //@ ensures List(this.getClass())(this, xs) &*& result == (xs == nil);
    
    int head();
        //@ requires List(this.getClass())(this, ?xs) &*& xs != nil;
        //@ ensures List(this.getClass())(this, xs) &*& result == head(xs);
    
    List tail();
        //@ requires List(this.getClass())(this, ?xs) &*& xs != nil;
        //@ ensures List(this.getClass())(this, xs) &*& result != null &*& List(result.getClass())(result, tail(xs));
    
    List map(MapFunc f);
        //@ requires List(this.getClass())(this, ?xs) &*& f != null &*& MapFunc(f.getClass())(f, xs, ?ys, ?info);
        //@ ensures List(this.getClass())(this, xs) &*& result != null &*& List(result.getClass())(result, ?zs) &*& MapFunc(f.getClass())(f, nil, append(ys, zs), info);
    
    boolean equals(List other);
        //@ requires List(this.getClass())(this, ?xs) &*& other != null &*& List(other.getClass())(other, ?ys);
        //@ ensures List(this.getClass())(this, xs) &*& List(other.getClass())(other, ys) &*& result == (xs == ys);

}

/*@

predicate_family_instance List(Nil.class)(Nil l, list<int> xs) =
    l != null &*& xs == nil;

@*/

class Nil implements List {

    Nil()
        //@ requires true;
        //@ ensures List(Nil.class)(this,nil);
    {
        //@ close List(Nil.class)(this, nil);
    }
    boolean isEmpty()
        //@ requires List(Nil.class)(this, ?xs);
        //@ ensures List(Nil.class)(this, xs) &*& result == (xs == nil);
    {
        //@ open List(Nil.class)(this, xs);
        //@ close List(Nil.class)(this, xs);
        return true;
    }
    
    int head()
        //@ requires List(Nil.class)(this, ?xs) &*& xs != nil;
        //@ ensures List(Nil.class)(this, xs) &*& result == head(xs);
    {
        //@ open List(Nil.class)(this, xs);
        return 0; //~allow_dead_code
    }
    
    List tail()
        //@ requires List(Nil.class)(this, ?xs) &*& xs != nil;
        //@ ensures List(Nil.class)(this, xs) &*& result != null &*& List(result.getClass())(result, tail(xs));
    {
        //@ open List(Nil.class)(this, xs);
        return null; //~allow_dead_code
    }
    
    List map(MapFunc f)
        //@ requires List(Nil.class)(this, ?xs) &*& f != null &*& MapFunc(f.getClass())(f, xs, ?ys, ?info);
        //@ ensures List(Nil.class)(this, xs) &*& result!= null &*& List(result.getClass())(result, ?zs) &*& MapFunc(f.getClass())(f, nil, append(ys, zs), info);
    {
        //@ open List(Nil.class)(this, xs);
        //@ close List(Nil.class)(this, xs);
        //@ append_nil(ys);
        //@ assume(this.getClass() == Nil.class);
        //@ list_split_fractions(this);
        return this;
    }
    
    boolean equals(List other)
        //@ requires List(Nil.class)(this, ?xs) &*& other!= null &*& List(other.getClass())(other, ?ys);
        //@ ensures List(Nil.class)(this, xs) &*& List(other.getClass())(other, ys) &*& result ? xs == ys : xs != ys;
    {
        //@ open List(Nil.class)(this, xs);
        //@ close List(Nil.class)(this, xs);
        return other.isEmpty();
    }

}

/*@

predicate_family_instance List(Cons.class)(Cons l, list<int> xs) =
    [_]l.head |-> ?head &*& [_]l.tail |-> ?tail &*& tail != null &*& List(tail.getClass())(tail, ?t) &*& xs == cons(head, t);

@*/

class Cons implements List {

    int head;
    List tail;
    
    Cons(int head, List tail)
        //@ requires tail != null &*& List(tail.getClass())(tail, ?t);
        //@ ensures List(Cons.class)(this, cons(head, t));
    {
        this.head = head;
        this.tail = tail;
        //@ close List(Cons.class)(this, cons(head, t));
    }

    boolean isEmpty()
        //@ requires List(Cons.class)(this, ?xs);
        //@ ensures List(Cons.class)(this, xs) &*& result == (xs == nil);
    {
        //@ open List(Cons.class)(this, ?xs_);
        //@ close List(Cons.class)(this, xs_);
        return false;
    }
    
    int head()
        //@ requires List(Cons.class)(this, ?xs) &*& xs != nil;
        //@ ensures List(Cons.class)(this, xs) &*& result == head(xs);
    {
        //@ open List(Cons.class)(this, ?xs_);
        return this.head;
        //@ close List(Cons.class)(this, xs_);
    }
    
    List tail()
        //@ requires List(Cons.class)(this, ?xs) &*& xs != nil;
        //@ ensures List(Cons.class)(this, xs) &*& result!= null &*& List(result.getClass())(result, tail(xs));
    {
        //@ open List(Cons.class)(this, ?xs_);
        List result = this.tail;
        //@ list_split_fractions(result);
        //@ close List(Cons.class)(this, xs_);
        return result;
    }
    
    List map(MapFunc f)
        //@ requires List(Cons.class)(this, ?xs) &*& f != null &*& MapFunc(f.getClass())(f, xs, ?ys, ?info);
        //@ ensures List(Cons.class)(this, xs) &*& result != null &*& List(result.getClass())(result, ?zs) &*& MapFunc(f.getClass())(f, nil, append(ys, zs), info);
    {
        //@ open List(Cons.class)(this, ?xs_);
        int fhead = f.apply(this.head);
        List tail = this.tail;
        List ftail = tail.map(f);
        //@ assert List(_)(ftail, ?ftailxs);
        return new Cons(fhead, ftail);
        //@ close List(Cons.class)(this, xs_);
        //@ append_assoc(ys, cons(fhead, nil), ftailxs);
    }
    
    boolean equals(List other)
        //@ requires List(Cons.class)(this, ?xs) &*& other != null &*& List(other.getClass())(other, ?ys);
        //@ ensures List(Cons.class)(this, xs) &*& List(other.getClass())(other, ys) &*& result ? xs == ys : xs != ys;
    {
        //@ switch (ys) { case nil: case cons(h, t): }
        //@ open List(Cons.class)(this, ?xs_);
        boolean otherEmpty = other.isEmpty();
        if (otherEmpty) {
            //@ close List(Cons.class)(this, xs_);
            return false;
        } else {
            int otherHead = other.head();
            if (this.head == otherHead) {
                List otherTail = other.tail();
                List tail = this.tail;
                return tail.equals(otherTail);
                //@ close List(Cons.class)(this, xs_);
            } else {
                //@ close List(Cons.class)(this, xs_);
                return false;
            }
        }
    }

}

/*@

fixpoint list<int> plusOne(list<int> xs) {
    switch (xs) {
        case nil: return nil;
        case cons(h, t): return cons<int>(h + 1, plusOne(t));
    }
}

predicate_family_instance MapFunc(PlusOne.class)(PlusOne f, list<int> in, list<int> out, list<int> info) =
    plusOne(info) == append(out, plusOne(in));

@*/

class PlusOne implements MapFunc {

    PlusOne()
        //@ requires true;
        //@ ensures true;
    {
    }
    
    int apply(int x)
        //@ requires MapFunc(PlusOne.class)(this, ?in, ?out, ?info) &*& switch (in) { case nil: return false; case cons(h, t): return x == h; };
        //@ ensures MapFunc(PlusOne.class)(this, tail(in), append(out, cons(result, nil)), info);
    {
        //@ open MapFunc(PlusOne.class)(this, ?in_, ?out_, ?info_);
        //@ append_assoc(out_, cons(x + 1, nil), plusOne(tail(in_)));
        //@ close MapFunc(PlusOne.class)(this, tail(in_), append(out_, cons(x + 1, nil)), info_);
        return x + 1;
    }
    
}

class Program {
    public static void main(String[] args)
    //@ requires true;
    //@ ensures true;
    {
        List l = new Nil();
        l = new Cons(3, l);
        l = new Cons(2, l);
        l = new Cons(1, l);
        PlusOne f = new PlusOne();
        //@ close MapFunc(PlusOne.class)(f, cons(1, cons(2, cons(3, nil))), nil, cons(1, cons(2, cons(3, nil))));
        List l2 = l.map(f);
        //@ open MapFunc(PlusOne.class)(f, nil, ?ys, cons(1, cons(2, cons(3, nil))));
        List l3 = new Nil();
        l3 = new Cons(4, l3);
        l3 = new Cons(3, l3);
        l3 = new Cons(2, l3);
        boolean eq = l2.equals(l3);
        //@ append_nil(ys);
        assert(eq);
    }
}
