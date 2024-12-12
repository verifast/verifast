//@ #include "list.gh"
//@ #include "arrays.gh"

/*@
lemma_auto void append_all_eq<t>(list<t> vs1, list<t> vs2, t val)
requires all_eq(vs1, val) && all_eq(vs2, val);
ensures all_eq(append(vs1, vs2), val) == true;
{
    switch (vs1) {
        case nil: return;
        case cons(a, b): {
            append_all_eq(b, vs2, val);
        };
    }
}
@*/

struct wrapper {
    int values[2][4][3];
};

void fill(int *buf, int len, int val)
//@ requires ints_(buf, len, _) &*& len >= 0;
//@ ensures ints(buf, len, ?vs) &*& all_eq(vs, val) == true;
{
    for (int i = 0; i < len; ++i)
    //@ invariant ints(buf, i, ?vs) &*& all_eq(vs, val) == true &*& ints_(buf + i, len - i, _);
    {
        buf[i] = val;
        //@ close ints(buf + i, 1, _);
        //@ ints_join(buf);
    }
}

struct S {
    int i;
};

void init_list()
//@ requires true;
//@ ensures true;
{
    int matrix2[4][5] = { { 0, 0, 0, 0, 0 }, { 2, 2, 2, 2, 2 } };
    matrix2[1][4] = 10;
    //@ chars__to_ints_(matrix2[2], 10);
    //@ ints__split(matrix2[2], 1 * 5 + 4);
    matrix2[3][4] = 10;
    //@ close ints_(matrix2[3] + 4, 1, _);
    
    //@ ints__join(matrix2[2]);
    //@ ints_join(matrix2);
    //@ ints_to_ints_(matrix2);
    //@ ints__join(matrix2);
}

int main()
//@ requires true;
//@ ensures true;       
{
    int matrix1[10][8];
    //@ chars__to_ints_(matrix1, 80);
    fill(matrix1, 80, 4);
    
    struct S structs[4][2];
    //@ chars__split((void *) structs, (2 * 2 + 1) * sizeof(struct S));
    //@ close_struct(structs[0]);
    //@ close_struct(structs[2] + 1);
    
    struct wrapper w;
    //@ chars__split((void *) w.values, (1 * 4 * 3 + 3 * 3 + 2) * sizeof(int));
    w.values[1][3][2] = 6;
    
    //@ integer_to_chars(w.values[1][3] + 2);
    //@ chars_to_chars_((void *) (w.values[1][3] + 2));
    
    //@ open_struct(structs[2] + 1);
    //@ open_struct(structs[0]);
    //@ chars__join((void *) structs);
    //@ chars__join((void *) structs);
    
    //@ ints_to_chars(matrix1);
    return 0;
}