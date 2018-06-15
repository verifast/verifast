#include "stdlib.h"

void modify_int_refs_old_syntax(int* first, int* second)
    //@ requires integer(first, ?val1) &*& integer(second, ?val2);
    //@ ensures integer(first, val1 + 1) &*& integer(second, val2 - 1);
{
    (*first)++;
    (*second)--;
}

void modify_int_refs_new_syntax(int* first, int* second)
    //@ requires *first |-> ?val1 &*& *second |-> ?val2;
    //@ ensures *first |-> val1 + 1 &*& *second |-> val2 - 1;
{
    (*first)++;
    (*second)--;
}

//@ predicate intptr_pointsto(int **p; int *v) = *p |-> v;

void modify_uint_refs_old_syntax(unsigned int* first, unsigned int* second)
    //@ requires u_integer(first, ?val1) &*& u_integer(second, ?val2);
    //@ ensures u_integer(first, val1 + 1) &*& u_integer(second, val2 - 1);
{
    *first = *first + 1;
    *second = *second - 1;
}

void modify_uint_refs_new_syntax(unsigned int* first, unsigned int* second)
    //@ requires *first |-> ?val1 &*& *second |-> ?val2;
    //@ ensures *first |-> val1 + 1 &*& *second |-> val2 - 1;
{
    *first = *first + 1;
    *second = *second - 1;
}

void modify_char_refs_old_syntax(char* first, char* second)
    //@ requires character(first, ?val1) &*& character(second, ?val2);
    //@ ensures character(first, (char) (val1 + 1)) &*& character(second, (char) (val2 - 1));
{
    (*first)++;
    (*second)--;
}

void modify_char_refs_new_syntax(char* first, char* second)
    //@ requires *first |-> ?val1 &*& *second |-> ?val2;
    //@ ensures *first |-> (char) (val1 + 1) &*& *second |-> (char) (val2 - 1);
{
    (*first)++;
    (*second)--;
}

void modify_calculated_address_new_syntax(int* foo)
    //@ requires *(foo + 1) |-> ?val1 &*& *(foo + 2) |-> ?val2;
    //@ ensures *(foo + 1) |-> val1 + 5 &*& *(foo + 2) |-> val2 - 5;
{
    *(foo + 1) = *(foo + 1) + 5;
    *(foo + 2) = *(foo + 2) - 5;
}

void modify_array_new_syntax(int* foo)
    //@ requires foo[1] |-> ?val1 &*& foo[2] |-> ?val2;
    //@ ensures foo[1] |-> val1 + 5 &*& foo[2] |-> val2 - 5;
{
    *(foo + 1) = *(foo + 1) + 5;
    *(foo + 2) = *(foo + 2) - 5;
}

int main() //@ : main
    //@ requires true;
    //@ ensures true;
{
    int i = -10;
    int j = 10;
    unsigned int k = 10;
    unsigned int l = 20;
    char m = 'a';
    char n = 'z';
    int* int_pointer;
    
    //@ assert i == -10 && j == 10;
    modify_int_refs_old_syntax(&i, &j);
    //@ assert i == -9 && j == 9;
    modify_int_refs_new_syntax(&i, &j);
    //@ assert i == -8 && j == 8;

    
    //@ assert k == 10 && l == 20;
    modify_uint_refs_old_syntax(&k, &l);
    //@ assert k == 11 && l == 19;
    modify_uint_refs_new_syntax(&k, &l);
    //@ assert k == 12 && l == 18;    
    
    
    //@ assert m == 'a' && n == 'z';
    modify_char_refs_old_syntax(&m, &n);
    //@ assert m == 'b' && n == 'y';
    modify_char_refs_new_syntax(&m, &n);
    //@ assert m == 'c' && n == 'x';
    
    
    int_pointer = malloc(5 * sizeof(int));
    if (int_pointer == 0) abort();
    //@ open ints(int_pointer, _, _);
    *(int_pointer + 1) = 5;
    *(int_pointer + 2) = 5;
    
    //@ assert integer(int_pointer + 1, 5) &*& integer(int_pointer + 2, 5);
    modify_calculated_address_new_syntax(int_pointer);
    //@ assert *(int_pointer + 1) |-> 10 &*& *(int_pointer + 2) |-> 0;
    modify_array_new_syntax(int_pointer);
    //@ assert int_pointer[1] |-> 15 &*& int_pointer[2] |-> -5;
        
    free(int_pointer);
    
    
    return 0;
}


