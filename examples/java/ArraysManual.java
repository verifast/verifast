class LimitsTest {
    static void test(byte[] xs, byte[] ys)
        //@ requires xs[0..10] |-> _ &*& ys[0] |-> _;
        //@ ensures true;
    {
        int x = xs[0];
        assert -128 <= x && x <= 127;
        int y = ys[0];
        assert -128 <= y && y <= 127;
    }
}

class AutoSliceUpcastTest {
    static void foo(Object[] xs)
        //@ requires [?f]array_slice(xs, 0, xs.length, ?elems);
        //@ ensures [f]array_slice(xs, 0, xs.length, elems);
    {
    }
    
    static void bar(Integer[] xs)
        //@ requires [_]xs[..] |-> ?elems;
        //@ ensures [_]xs[..] |-> elems;
    {
        // Here, an auto-upcast of the array_slice chunk happens.
        // This leaks half of the fraction (to prevent assignment, which may raise ArrayStoreException).
        // Only makes sense for read-only arrays.
        foo(xs);
    }
}
    
class AutoSliceUpcastTest1 {
    static void foo(Object[] xs)
        //@ requires [?f]xs[..] |-> ?elems;
        //@ ensures [f]xs[..] |-> elems;
    {
    }
    
    static void bar(Integer[] xs)
        //@ requires [_]xs[..] |-> ?elems;
        //@ ensures [_]xs[..] |-> elems;
    {
        // Here, an auto-upcast of the array_slice chunk happens.
        // This leaks half of the fraction (to prevent assignment, which may raise ArrayStoreException).
        // Only makes sense for read-only arrays.
        foo(xs);
    }
}

class InitTest {
    static void test()
        //@ requires true;
        //@ ensures true;
    {
        int[] xs = new int[] { 1, 2, 3 };
        assert xs.length == 3;
        int x = xs[0];
        assert x == 1;
        x = xs[1];
        assert x == 2;
        x = xs[2];
        assert x == 3;
    }
}

class Incrementor {
    static void increment(int[] xs, int i)
        //@ requires xs[i] |-> ?n;
        //@ ensures xs[i] |-> n + 1;
    {
        xs[i]++;
    }
}

class Person {
    int age;
}

//@ predicate person(int minAge, Person person; int age) = person.age |-> age &*& minAge <= age;

class Persons {
    Person[] persons;
    
    void processBirthday(int i)
        //@ requires this.persons |-> ?persons &*& array_slice_deep(persons, 0, persons.length, person, 18, _, _) &*& 0 <= i &*& i < persons.length;
        //@ ensures this.persons |-> persons &*& array_slice_deep(persons, 0, persons.length, person, 18, _, _);
    {
        Person p = this.persons[i];
        p.age++;
    }
}

//@ predicate record(int recordLength, Object record; unit value) = array_slice<byte>(^record, 0, recordLength, _) &*& value == unit;

/*@

lemma void all_eq_take<t>(int n, list<t> xs, t x)
    requires 0 <= n &*& n <= length(xs) &*& all_eq(xs, x) == true;
    ensures all_eq(take(n, xs), x) == true;
{
    switch (xs) {
        case nil:
        case cons(x0, xs0):
            if (n == 0) {
            } else {
                all_eq_take(n - 1, xs0, x);
            }
    }
}

@*/

class ArrayTest {
    static void test(Object[] a, int i)
      /*@
      requires
          0 <= i &*&
          a[0..i + 10] |-> ?l &*&
          a[i + 10..i + 20] |-> ?l2 &*&
          a[i + 20..i + 35] |-> ?l3;
      @*/
      /*@
      ensures
          a[i..i + 30] |-> append(drop(i,l), append(l2, take(10,l3))) &*&
          a[0..i] |-> take(i, l) &*&
          a[i + 30..i + 35] |-> drop(10, l3);
      @*/
    {
    }
    
    static void testDeep(Object[] a, int i)
      /*@
      requires
          0 <= i &*&
          array_slice_deep(a, 0, i + 10, ?p, ?info, ?elems1, ?vs1) &*&
          array_slice_deep(a, i + 10, i + 20, p, info, ?elems2, ?vs2) &*&
          array_slice_deep(a, i + 20, i + 35, p, info, ?elems3, ?vs3);
      @*/
      /*@
      ensures
          array_slice_deep(a, i, i + 30, p, info, append(drop(i, elems1), append(elems2, take(10, elems3))), append(drop(i, vs1), append(vs2, take(10, vs3)))) &*&
          array_slice_deep(a, 0, i, p, info, take(i, elems1), take(i, vs1)) &*&
          array_slice_deep(a, i + 30, i + 35, p, info, drop(10, elems3), drop(10, vs3));
      @*/
    {
    }
    
    static void deleteRecord(Object[] records, int recordLength, int i)
        /*@
        requires
            array_slice_deep(records, 0, records.length, record, recordLength, ?rs, _) &*&
            0 <= i &*& i < records.length &*& 0 < recordLength;
        @*/
        //@ ensures array_slice_deep(records, 0, records.length, record, recordLength, _, _);
    {
        Object record0 = records[i];
        byte[] record = (byte[])record0;
        record[recordLength - 1] = 0;
    }
    
    static Object[] createRecords(int count, int recordLength)
        //@ requires 0 <= count &*& 0 <= recordLength;
        //@ ensures array_slice_deep(result, 0, result.length, record, recordLength, _, _);
    {
        Object[] records = new Object[count];
        int i = 0;
        while (i < count)
            //@ invariant 0 <= i &*& i <= count &*& array_slice_deep(records, 0, i, record, recordLength, _, _) &*& records[i..] |-> ?elems &*& all_eq(elems, null) == true;
        {
            Object tmp = records[i];
            assert tmp == null;
            records[i] = new byte[recordLength];
            i++;
        }
        return records;
    }

    static Object[] createRecords2(int count, int recordLength)
        //@ requires 0 <= count &*& 0 <= recordLength;
        //@ ensures array_slice_deep(result, 0, result.length, record, recordLength, _, _);
    {
        Object[] records = new Object[count];
        int i = count;
        while (0 < i)
            //@ invariant 0 <= i &*& i <= count &*& array_slice_deep(records, i, count, record, recordLength, _, _) &*& records[..i] |-> ?elems &*& all_eq(elems, null) == true;
        {
            i--;
            Object tmp = records[i];
            assert tmp == null;
            records[i] = new byte[recordLength];
            //@ all_eq_take(i, elems, null);
        }
        return records;
    }
}