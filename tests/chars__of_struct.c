#include <stdlib.h>
//@ #include <listex.gh>

void memcpy(void *array, void *array0, size_t count);
    //@ requires chars_(array, count, _) &*& [?f]chars_(array0, count, ?cs0);
    //@ ensures chars_(array, count, cs0) &*& [f]chars_(array0, count, cs0);

typedef struct Foo {
    int i;
    int j;
} Foo;

struct Foo *new_foo(int i)
//@ requires true;
//@ ensures malloc_block_Foo(result) &*& result->i |-> i &*& result->j |-> _ &*& result != 0;
{
    Foo *f = malloc(sizeof(Foo));
    if (f == 0) abort();
    f->i = i;
    return f;
} 

void memcpy_foo()
//@ requires true;
//@ ensures true;
{
    Foo *f = new_foo(10);
    Foo copy;
    copy.i = 4;
    //@ open_malloc_block(f);
    //@ open_struct(f);
    //@ open_struct(&copy);
    memcpy(&copy, f, sizeof(Foo));
    //@ close_struct(&copy);
    //@ close_struct(f);
    //@ close_malloc_block(f);
    
    //@ assert Foo_i_(f, ?i) &*& Foo_i_(&copy, i) &*& i == some(10);
    //@ assert Foo_j_(f, ?j) &*& Foo_j_(&copy, j);
    
    free(f);
}

typedef struct Pair {
    int first;
    int second;
} Pair;

typedef struct DoublePair {
    Pair first_pair;
    Pair second_pair;
} DoublePair;

void memcpy_struct_with_struct_as_field()
//@ requires true;
//@ ensures true;
{
    Pair p1;
    Pair p2;
    DoublePair dp;
    DoublePair dp_copy;
    
    p1.first = 1;
    p1.second = 2;

    dp.first_pair = p1;
    
    //@ open_struct(&dp);
    //@ open_struct(&dp_copy);
    memcpy(&dp_copy, &dp, sizeof(DoublePair));
    //@ close_struct(&dp);
    //@ close_struct(&dp_copy);
    
    //@ assert Pair_first_(&dp.first_pair, ?f) &*& Pair_first_(&dp_copy.first_pair, f) &*& f == some(1);
    //@ assert Pair_second_(&dp.first_pair, ?s) &*& Pair_second_(&dp_copy.first_pair, s) &*& s == some(2);
    
    //@ assert Pair_first_(&dp.second_pair, ?f_uninit) &*& Pair_first_(&dp_copy.second_pair, f_uninit);
    //@ assert Pair_second_(&dp.second_pair, ?s_uninit) &*& Pair_second_(&dp_copy.second_pair, s_uninit);
}

typedef struct Arr {
    int ints[10];
    int len;
} Arr;

void memcpy_array()
//@ requires true;
//@ ensures true;
{
    Arr a = {{1, 2, 3}, 3};
    Arr a_copy;
    Arr a_partial;
    
    //@ open_struct(&a);
    //@ open_struct(&a_copy);
    memcpy(&a_copy, &a, sizeof(Arr));
    //@ close_struct(&a_copy);
    //@ close_struct(&a);
    
    //@ assert Arr_len_(&a, ?l) &*& Arr_len_(&a_copy, l) &*& l == some(3);
    //@ assert ints(&a.ints, 10, ?vs) &*& ints(&a_copy.ints, 10, vs) &*& vs == {1, 2, 3, 0, 0, 0, 0, 0, 0, 0};
    
    a_partial.ints[0] = 1;
    a_partial.ints[1] = 2;
    a_partial.len = 2;
    
    //@ open_struct(&a_partial);
    //@ open_struct(&a_copy);
    memcpy(&a_copy, &a_partial, sizeof(Arr));
    //@ close_struct(&a_copy);
    //@ close_struct(&a_partial);   
    
    //@ assert Arr_len_(&a_partial, ?lp) &*& Arr_len_(&a_copy, lp) &*& lp == some(2);
    //@ assert ints_(&a_partial.ints, 10, ?vsp) &*& ints_(&a_copy.ints, 10, vsp) &*& nth(0, vsp) == some(1) &*& nth(1, vsp) == some(2);
}

void memcpy_array_of_structs()
//@ requires true;
//@ ensures true;
{
    Foo foos[5];
    //@ assert chars_((void *) foos, sizeof(foos), ?foos_chars_);
    Foo foos_copy[5];
    //@ close_struct(foos);
    foos[0].i = 0;
    //@ assert Foo_i_(foos, ?i0);
    
    //@ open_struct(foos);
    //@ assert chars_((void *) foos, sizeof(Foo), ?foo_chars__of);
    //@ take_append(sizeof(Foo), foo_chars__of, drop(sizeof(Foo), foos_chars_));
    memcpy(foos_copy, foos, sizeof(foos));
    
    //@ assert chars_((void *) foos, sizeof(Foo), ?vs) &*& chars_((void *) foos_copy, sizeof(Foo), vs);

    //@ close_struct(foos);
    //@ close_struct(foos_copy);
    //@ assert Foo_i_(foos, i0) &*& Foo_i_(foos_copy, i0) &*& i0 == some(0);
    //@ assert Foo_j_(foos, ?j0) &*& Foo_j_(foos_copy, j0);
    //@ open_struct(foos_copy);
    //@ open_struct(foos);
}