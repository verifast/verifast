//@ predicate record(int recordLength, Object record; unit value) = array_slice((byte[])record, 0, recordLength, _) &*& value == unit;

class ArrayTest {
    static void arraytest(Object[] a, int i)
      //@ requires 0<= i &*& array_slice(a, 0, i + 10, ?l) &*& array_slice(a, i + 10, i + 20, ?l2) &*& array_slice(a, i + 20, i + 35, ?l3);
      //@ ensures array_slice(a, i, i + 30, append(append(drop(i,l), l2),take(10,l3))) &*& array_slice(a, 0, i, take(i, l)) &*& array_slice(a, i + 30, i + 35, drop(10, l3));
      {
      }
    
    static void deleteRecord(Object[] records, int recordLength, int i)
        //@ requires records != null &*& array_slice_deep(records, 0, records.length, record, recordLength, ?rs, _) &*& 0 <= i &*& i < records.length &*& 0 < recordLength;
        //@ ensures array_slice_deep(records, 0, records.length, record, recordLength, _, _);
    {
        Object record0 = records[i];
        byte[] record = (byte[])record0;
        record[recordLength - 1] = 0;
        //@ close record(recordLength, record0, _);
        //@ array_slice_deep_close(records, i, @record, recordLength);
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
            //@ close record(recordLength, record, _);
            //@ array_slice_deep_close(records, i, @record, recordLength);
            i++;
        }
        return records;
    }
}