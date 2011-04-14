// TODO: Support lemma methods

class C {
    int x;
    
    C()
        //@ requires true;
        //@ ensures C(0, unit);
    {
        //@ close C(0, unit);
    }

    //@ predicate C(int x, any info) = this.x |-> x &*& info == unit;
}

class D extends C {
    int y;

    D()
        //@ requires true;
        //@ ensures D(0, 0, unit);
    {
        //@ close D(0, 0, unit);
    }
    
    /*@
    
    predicate C(int x, pair<int, any> info) = D(x, ?y, ?info0) &*& info == pair(y, info0);
    predicate D(int x, int y, any info) = this.C(C.class)(x, _) &*& this.y |-> y &*& info == unit;

    lemma void castCToD()
        requires C(?x, ?info);
        ensures switch (info) { case pair(y, info0): return D(x, y, info0); };
    {
        open C(x, _);
    }
    
    lemma void castDToC()
        requires D(?x, ?y, ?info);
        ensures C(x, pair(y, info));
    {
        close C(_, _);
    }
    
    @*/
    
    int getY()
        //@ requires D(?x, ?y, ?info);
        //@ ensures D(x, y, info) &*& result == y;
    {
        //@ open D(x, y, _);
        return this.y;
        //@ close D(x, y, _);
    }
}
class E extends D {
    int z;
    
    E()
        //@ requires true;
        //@ ensures E(0, 0, 0, unit);
    {
        //@ close E(0, 0, 0, unit);
    }
    
    /*@

    predicate C(int x, pair<int, pair<int, any> > info) = E(x, ?y, ?z, unit) &*& info == pair(y, pair(z, unit));
    predicate D(int x, int y, pair<int, any> info) = E(x, y, ?z, unit) &*& info == pair(z, unit);
    predicate E(int x, int y, int z, any info) = this.D(D.class)(x, y, _) &*& this.z |-> z &*& info == unit;

    lemma void castCToD()
        requires C(?x, ?info);
        ensures switch (info) { case pair(y, info0): return D(x, y, info0); };
    {
        open C(x, _);
        close D(x, _, _);
    }

    lemma void castDToC()
        requires D(?x, ?y, ?info);
        ensures C(x, pair(y, info));
    {
        open D(_, _, _);
        close C(_, _);
    }
    
    @*/
    
    int getY()
        //@ requires D(?x, ?y, ?info);
        //@ ensures D(x, y, info) &*& result == y;
    {
        //@ open D(x, y, _);
        //@ open E(x, y, _, _);
        return super.getY();
        //@ close E(x, y, _, _);
        //@ close D(x, y, _);
    }
}

//@ predicate getY_result(any info0) = true;

class Program {
    static int getY(C c)
        //@ requires c.C(?x, ?info);
        //@ ensures c.C(x, info) &*& true == (c instanceof D) ? getY_result(?info0) &*& info == pair(result, info0) : true;
    {
        if (c instanceof D) {
            D d = (D)c;
            //@ d.castCToD();
            //@ assert d.D(_, _, ?info0);
            //@ close getY_result(info0);
            return d.getY();
            //@ d.castDToC();
        } else {
            return 0;
        }
    }

    static void test()
        //@ requires true;
        //@ ensures true;
    {
        E e = new E();
        //@ close e.C(_, _);
        getY(e);
    }
}