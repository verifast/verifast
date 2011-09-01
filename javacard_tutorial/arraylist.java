class ArrayList {
    byte[] elems;
    short count;
    
    /*@
    predicate ArrayList(short n) =
        elems |-> ?es &*& count |-> n &*&
        array_slice(es, 0, n, _) &*& array_slice(es, n, es.length, _) &*&
        es.length <= 32767;
    @*/
        
    ArrayList(short size)
        //@ requires 0 <= size;
        //@ ensures ArrayList(0);
    {
        elems = new byte[size];
    }
    
    short getCount()
        //@ requires ArrayList(?n);
        //@ ensures ArrayList(n) &*& result == n;
    {
        return count;
    }
    
    byte get(short index)
        //@ requires ArrayList(?n) &*& 0 <= index &*& index < n;
        //@ ensures ArrayList(n);
    {
        return elems[index];
    }
    
    boolean add(byte value)
        //@ requires ArrayList(?n);
        //@ ensures result ? ArrayList((short)(n + 1)) : ArrayList(n);
    {
        if (count == elems.length)
            return false;
        elems[count++] = value;
        return true;
    }
}

class Program {
    static void test()
        //@ requires true;
        //@ ensures true;
    {
        ArrayList list = new ArrayList((short)10);
        if (list.add((byte)1) && list.add((byte)2) && list.add((byte)3)) {
            short count = list.getCount();
            assert count == 3;
            list.get((short)2);
        }
    }
}