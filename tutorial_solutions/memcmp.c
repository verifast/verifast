int memcmp(char *p1, char *p2, int count)
    //@ requires [?f1]p1[0..count] |-> ?cs1 &*& [?f2]p2[0..count] |-> ?cs2;
    //@ ensures [f1]p1[0..count] |-> cs1 &*& [f2]p2[0..count] |-> cs2 &*& (result == 0) == (cs1 == cs2);
{
    int result = 0;
    for (int i = 0; ; i++)
        //@ requires [f1]p1[i..count] |-> ?xs1 &*& [f2]p2[i..count] |-> ?xs2 &*& result == 0;
        //@ ensures [f1]p1[old_i..count] |-> xs1 &*& [f2]p2[old_i..count] |-> xs2 &*& (result == 0) == (xs1 == xs2);
    {
        //@ open chars(p1 + i, _, _);
        //@ open chars(p2 + i, _, _);
        if (i == count) {
            break;
        }
        if (p1[i] < p2[i]) {
            result = -1; break;
        }
        if (p1[i] > p2[i]) {
            result = 1; break;
        }
    }
    return result;
}