class Foo {}
/*@

inductive list<t> = nil | cons(t, list<t>);

fixpoint list<t> list_add<t>(list<t> xs, t x) {
    switch (xs) {
        case nil: return cons(x, nil);
        case cons(h, t): return cons(h, list_add(t, x));
    }
}

fixpoint list<t> append<t>(list<t> xs, list<t> ys) {
    switch (xs) {
        case nil: return ys;
        case cons(h, t): return cons(h, append(t, ys));
    }
}

lemma void append_nil<t>(list<t> xs)
    requires true;
    ensures append(xs, nil) == xs;
{
    switch (xs) {
        case nil:
        case cons(h, t): append_nil(t);
    }
}

lemma void append_add<t>(list<t> xs, t y, list<t> ys)
    requires true;
    ensures append(list_add(xs, y), ys) == append(xs, cons(y, ys));
{
    switch (xs) {
        case nil:
        case cons(h, t):
            append_add(t, y, ys);
    }
}

fixpoint list<t> tail<t>(list<t> xs) {
    switch (xs) {
        case nil: return nil;
        case cons(h, t): return t;
    }
}

predicate_family MapFunc(Class c)(MapFunc f, list<int> in, list<int> out, any info);

@*/

interface MapFunc {

    int apply(int x);
        //@ requires MapFunc(this.getClass())(this, ?in, ?out, ?info) &*& switch (in) { case nil: return false; case cons(h, t): return x == h; };
        //@ ensures MapFunc(this.getClass())(this, tail(in), list_add(out, result), info);

}

/*@

predicate_family List(Class c)(List l, list<int> xs);

lemma void list_split_fractions(List l);
    requires [_]List(l.getClass())(l, ?xs);
    ensures List(l.getClass())(l, xs) &*& List(l.getClass())(l, xs);

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
        //@ ensures List(this.getClass())(this, xs) &*& List(result.getClass())(result, tail(xs));
    
    List map(MapFunc f);
        //@ requires List(this.getClass())(this, ?xs) &*& MapFunc(f.getClass())(f, xs, ?ys, ?info);
        //@ ensures List(this.getClass())(this, xs) &*& List(result.getClass())(result, ?zs) &*& MapFunc(f.getClass())(f, nil, append(ys, zs), info);
    
    boolean equals(List other);
        //@ requires List(this.getClass())(this, ?xs) &*& List(other.getClass())(other, ?ys);
        //@ ensures List(this.getClass())(this, xs) &*& List(other.getClass())(other, ys) &*& result == (xs == ys);

}

/*@

predicate_family_instance List(Nil.class)(Nil l, list<int> xs) =
    xs == nil;

@*/

class Nil implements List {

    Nil()
        //@ requires true;
        //@ ensures List(Nil.class)(result,nil);
    {
        //@ close List(Nil.class)(this, nil);
    }
    boolean isEmpty()
    {
        //@ open List(Nil.class)(this, xs);
        //@ close List(Nil.class)(this, xs);
        return true;
    }
    
    int head()
    {
        //@ open List(Nil.class)(this, xs);
        //@ close List(Nil.class)(this, xs);
        return 0;
    }
    
    List tail()
    {
        //@ open List(Nil.class)(this, xs);
        //@ close List(Nil.class)(this, xs);
        return null;
    }
    
    List map(MapFunc f)
    {
        //@ open List(Nil.class)(this, xs);
        //@ close List(Nil.class)(this, xs);
        //@ list_split_fractions(this);
        //@ append_nil(ys);
        return this;
    }
    
    boolean equals(List other)
    {
        //@ open List(Nil.class)(this, xs);
        //@ close List(Nil.class)(this, xs);
        boolean result = other.isEmpty();
        return result;
    }

}

/*@

predicate_family_instance List(Cons.class)(Cons l, list<int> xs) =
    [_]l.head |-> ?head &*& [_]l.tail |-> ?tail &*& List(tail.getClass())(tail, ?t) &*& xs == cons(head, t);

@*/

class Cons implements List {

    int head;
    List tail;
    
    Cons(int head, List tail)
        //@ requires List(tail.getClass())(tail, ?t);
        //@ ensures List(Cons.class)(result, cons(head, t));
    {
        this.head = head;
        this.tail = tail;
        //@ close List(Cons.class)(this, cons(head, t));
    }

    boolean isEmpty()
    {
        //@ open List(Cons.class)(this, ?xs_);
        //@ close List(Cons.class)(this, xs_);
        return false;
    }
    
    int head()
    {
        //@ open List(Cons.class)(this, ?xs_);
        int result = this.head;
        //@ close List(Cons.class)(this, xs_);
        return result;
    }
    
    List tail()
    {
        //@ open List(Cons.class)(this, ?xs_);
        List result = this.tail;
        //@ list_split_fractions(result);
        //@ close List(Cons.class)(this, xs_);
        return result;
    }
    
    List map(MapFunc f)
    {
        //@ open List(Cons.class)(this, ?xs_);
        int fhead = f.apply(this.head);
        List tail = this.tail;
        List ftail = tail.map(f);
        //@ assert List(_)(ftail, ?ftailxs);
        List result = new Cons(fhead, ftail);
        //@ close List(Cons.class)(this, xs_);
        //@ append_add(ys, fhead, ftailxs);
        return result;
    }
    
    boolean equals(List other)
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
                boolean tmp = tail.equals(otherTail);
                //@ close List(Cons.class)(this, xs_);
                return tmp;
            } else {
                //@ close List(Cons.class)(this, xs_);
                return false;
            }
        }
    }

}

/*@

fixpoint int head(list<int> xs) {
    switch (xs) {
        case nil: return 0;
        case cons(h, t): return h;
    }
}
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
    {
        //@ open MapFunc(PlusOne.class)(this, ?in_, ?out_, ?info_);
        //@ append_add(out_, x + 1, plusOne(tail(in_)));
        //@ close MapFunc(PlusOne.class)(this, tail(in_), list_add(out_, x + 1), info_);
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
