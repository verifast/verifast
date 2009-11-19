/*@

lemma void array_slice_inv<T>(T[] array, int start);
    requires [?f]array_slice<T>(array, start, ?end, ?elems);
    ensures [f]array_slice<T>(array, start, end, elems) &*& array != null &*& 0 <= start &*& start <= end &*& end <= array.length &*& start + length(elems) == end;

lemma void array_slice_deep_close<T, A, V>(T[] array, int start, predicate(A, T, V) p, A a);
    requires array_slice<T>(array, start, start + 1, ?elems) &*& p(a, head(elems), ?v);
    ensures array_slice_deep<T, A, V>(array, start, start + 1, p, a, elems, cons(v, nil));

lemma void array_slice_deep_open<T, A, V>(T[] array, int start);
    requires array_slice_deep<T, A, V>(array, start, start + 1, ?p, ?a, ?elems, ?vs);
    ensures array_slice<T>(array, start, start + 1, elems) &*& p(a, head(elems), head(vs));

lemma void array_slice_split<T>(T[] array, int start, int start1);
    requires array_slice<T>(array, start, ?end, ?elems) &*& start <= start1 &*& start1 <= end;
    ensures
        array_slice<T>(array, start, start1, take(start1 - start, elems)) &*&
        array_slice<T>(array, start1, end, drop(start1 - start, elems)) &*&
        elems == append(take(start1 - start, elems), drop(start1 - start, elems));

lemma void array_slice_join<T>(T[] array, int start);
    requires
        array_slice<T>(array, start, ?start1, ?elems1) &*& array_slice<T>(array, start1, ?end, ?elems2);
    ensures array_slice<T>(array, start, end, append(elems1, elems2));

lemma void array_slice_deep_split<T, A, V>(T[] array, int start, int start1);
    requires array_slice_deep<T, A, V>(array, start, ?end, ?p, ?a, ?elems, ?vs) &*& start <= start1 &*& start1 <= end;
    ensures
        array_slice_deep<T, A, V>(array, start, start1, p, a, take(start1 - start, elems), take(start1 - start, vs)) &*&
        array_slice_deep<T, A, V>(array, start1, end, p, a, drop(start1 - start, elems), drop(start1 - start, vs));

lemma void array_slice_deep_join<T, A, V>(T[] array, int start);
    requires
        array_slice_deep<T, A, V>(array, start, ?start1, ?p, ?a, ?elems1, ?vs1) &*&
        array_slice_deep<T, A, V>(array, start1, ?end, p, a, ?elems2, ?vs2);
    ensures array_slice_deep<T, A, V>(array, start, end, p, a, append(elems1, elems2), append(vs1, vs2));

lemma void array_slice_deep_empty_close<T, A, V>(T[] array, int start, predicate(A, T, V) p, A a);
    requires array != null &*& 0 <= start &*& start <= array.length;
    ensures array_slice_deep<T, A, V>(array, start, start, p, a, nil, nil);

@*/

//@ predicate record(int recordLength, Object record, unit value) = array_slice((byte[])record, 0, recordLength, _) &*& value == unit;

class ArrayTest {
    static void deleteRecord(Object[] records, int recordLength, int i)
        //@ requires records != null &*& array_slice_deep(records, 0, records.length, record, recordLength, ?rs, _) &*& 0 <= i &*& i < records.length &*& 0 < recordLength;
        //@ ensures array_slice_deep(records, 0, records.length, record, recordLength, _, _);
    {
        //@ array_slice_deep_split(records, 0, i);
        //@ array_slice_deep_split(records, i, i + 1);
        //@ array_slice_deep_open(records, i);
        Object record0 = records[i];
        //@ open record(recordLength, record0, _);
        byte[] record = (byte[])record0;
        //@ array_slice_split(record, 0, recordLength - 1);
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
            //@ array_slice_split(records, i, i + 1);
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