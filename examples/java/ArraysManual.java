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
        //@ requires this.persons |-> ?persons &*& persons != null &*& array_slice_deep(persons, 0, persons.length, person, 18, _, _) &*& 0 <= i &*& i < persons.length;
        //@ ensures this.persons |-> persons &*& array_slice_deep(persons, 0, persons.length, person, 18, _, _);
    {
        Person p = this.persons[i];
        p.age++;
    }
}

//@ predicate record(int recordLength, Object record; unit value) = array_slice((byte[])record, 0, recordLength, _) &*& value == unit;

class ArrayTest {
    static void test(Object[] a, int i)
      /*@
      requires
          0 <= i &*&
          array_slice(a, 0, i + 10, ?l) &*&
          array_slice(a, i + 10, i + 20, ?l2) &*&
          array_slice(a, i + 20, i + 35, ?l3);
      @*/
      /*@
      ensures
          array_slice(a, i, i + 30, append(drop(i,l), append(l2, take(10,l3)))) &*&
          array_slice(a, 0, i, take(i, l)) &*&
          array_slice(a, i + 30, i + 35, drop(10, l3));
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
            records != null &*&
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
            //@ invariant 0 <= i &*& i <= count &*& array_slice_deep(records, 0, i, record, recordLength, _, _) &*& array_slice(records, i, records.length, ?elems) &*& all_eq(elems, null) == true;
        {
            Object tmp = records[i];
            assert tmp == null;
            byte[] record = new byte[recordLength];
            records[i] = record;
            i++;
        }
        return records;
    }
}