//@ predicate record(int recordLength, Object record, unit value) = array_slice((byte[])record, 0, recordLength, _) &*& value == unit;

class ArrayTest {
    static void deleteRecord(Object[] records, int recordLength, int i)
        //@ requires records != null &*& array_slice_deep(records, 0, records.length, record, recordLength, ?rs, _) &*& 0 <= i &*& i < records.length &*& 0 < recordLength;
        //@ ensures array_slice_deep(records, 0, records.length, record, recordLength, _, _);
    {
        Object record0 = records[i];
        //@ open record(recordLength, record0, _);
        byte[] record = (byte[])record0;
        //@ produce_limits(recordLength);
        record[recordLength - 1] = 0;
        //@ array_slice_join(record, 0);
        //@ close record(recordLength, record0, _);
        //@ array_slice_deep_close(records, i, @record, recordLength);
        //@ array_slice_deep_join(records, 0);
        //@ array_slice_deep_join(records, 0);
    }
    
    static Object[] createRecords(int count, int recordLength)
        //@ requires 0 <= count &*& 0 <= recordLength;
        //@ ensures array_slice_deep(result, 0, result.length, record, recordLength, _, _);
    {
        Object[] records = new Object[count];
        //@ produce_limits(count);
        int i = 0;
        //@ array_slice_deep_empty_close(records, 0, record, recordLength);
        while (i < count)
            //@ invariant 0 <= i &*& i <= count &*& array_slice_deep(records, 0, i, record, recordLength, _, _) &*& array_slice(records, i, records.length, ?elems) &*& all_eq(elems, null) == true;
        {
            Object tmp = records[i];
            assert tmp == null;
            byte[] record = new byte[recordLength];
            records[i] = record;
            //@ close record(recordLength, record, _);
            //@ array_slice_deep_close(records, i, @record, recordLength);
            //@ array_slice_deep_join(records, 0);
            i++;
        }
        return records;
    }
}