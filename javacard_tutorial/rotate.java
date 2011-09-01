class Program {
    static void rotate(byte[] xs, short start, short end)
        //@ requires array_slice(xs, start, end, _);
        //@ ensures array_slice(xs, start, end, _);
    {
        if (start >= end - 1)
            return;
        byte last = xs[end - 1];
        for (short i = start; i < end - 1; i++)
            //@ invariant array_slice(xs, start, end, _) &*& start <= i;
        {
            xs[i + 1] = xs[i];
        }
        xs[start] = last;
    }
}