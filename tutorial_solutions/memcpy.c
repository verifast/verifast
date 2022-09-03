void memcpy(char *dest, char *src, int count)
    //@ requires chars_(dest, count, _) &*& [?f]chars(src, count, ?cs);
    //@ ensures chars(dest, count, cs) &*& [f]chars(src, count, cs);
{
    for (int i = 0; ; i++)
        //@ requires chars_(dest + i, count - i, _) &*& [f]chars(src + i, count - i, ?cs0);
        //@ ensures chars(dest + old_i, count - old_i, cs0) &*& [f]chars(src + old_i, count - old_i, cs0);
    {
        //@ open chars_(dest + i, _, _);
        //@ open chars(src + i, _, _);
        if (i == count) {
            break;
        }
        dest[i] = src[i];
    }
}

void memcpy1(char *dest, char *src, int count) // Identical but uses array slice syntax.
    //@ requires dest[0..count] |-> _ &*& [?f]src[0..count] |-> ?cs;
    //@ ensures dest[0..count] |-> cs &*& [f]src[0..count] |-> cs;
{
    for (int i = 0; ; i++)
        //@ requires dest[i..count] |-> _ &*& [f]src[i..count] |-> ?cs0;
        //@ ensures dest[old_i..count] |-> cs0 &*& [f]src[old_i..count] |-> cs0;
    {
        //@ open chars_(dest + i, _, _);
        //@ open chars(src + i, _, _);
        if (i == count) {
            break;
        }
        dest[i] = src[i];
    }
}

void test()
    //@ requires true;
    //@ ensures true;
{
    char buffer1[7] = "Hello!";
    char buffer2[7];
    memcpy(buffer2, buffer1, 7);
    assert(buffer2[5] == '!');
}