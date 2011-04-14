class C {
    int x;
    
    C()
        //@ requires true;
        //@ ensures C(0);
    {
        //@ close C(0);
    }

    //@ predicate C(int x) = this.x |-> x;
}

class D extends C {
    int y;

    D()
        //@ requires true;
        //@ ensures D(0, 0);
    {
        //@ close D(0, 0);
    }
    
    /*@
    
    predicate C(int x) = D(x, _);
    predicate D(int x, int y) = this.C(C.class)(x) &*& this.y |-> y;

    lemma void castCToD()
        requires C(?x);
        ensures D(x, _);
    {
        open C(x);
    }
    
    lemma void castDToC()
        requires D(?x, _);
        ensures C(x);
    {
        close C(_);
    }
    
    @*/
    
    int getY()
        //@ requires D(?x, ?y);
        //@ ensures D(x, y) &*& result == y;
    {
        //@ open D(x, y);
        return this.y;
        //@ close D(x, y);
    }
}

class E extends D {
    int z;
    
    E()
        //@ requires true;
        //@ ensures E(0, 0, 0);
    {
        //@ close E(0, 0, 0);
    }
    
    /*@

    predicate C(int x) = E(x, _, _);
    predicate D(int x, int y) = E(x, y, _);
    predicate E(int x, int y, int z) = this.D(D.class)(x, y) &*& this.z |-> z;

    lemma void castCToD()
        requires C(?x);
        ensures D(x, _);
    {
        open C(x);
        close D(x, _);
    }

    lemma void castDToC()
        requires D(?x, _);
        ensures C(x);
    {
        open D(_, _);
        close C(_);
    }
    
    @*/
    
    int getY()
        //@ requires D(?x, ?y);
        //@ ensures D(x, y) &*& result == y;
    {
        //@ open D(x, y);
        //@ open E(x, y, _);
        return super.getY();
        //@ close E(x, y, _);
        //@ close D(x, y);
    }
}

class Program {
    static int getY(C c)
        //@ requires c.C(?x);
        //@ ensures c.C(x);
    {
        if (c instanceof D) {
            D d = (D)c;
            //@ d.castCToD();
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
        //@ close e.C(_);
        getY(e);
    }
}