#include <stdlib.h>
#include <stdio.h>
#include <string.h>
//@ #include <listex.gh>

int read_int()
    //@ requires true;
    //@ ensures true;
{
    int x;
    int scanf_result = scanf("%i", &x);
    if (scanf_result < 1) abort();
    return x;
}

char *read_line()
    //@ requires true;
    //@ ensures string(result, ?cs) &*& malloc_block_chars(result, length(cs) + 1);
{
    char buffer[100];
    int scanf_result = scanf(" %99[^\n]", buffer);
    if (scanf_result < 1) abort();
    //@ chars_separate_string(buffer);
    char *result = strdup(buffer);
    //@ chars_unseparate_string(buffer);
    if (result == 0) abort();
    return result;
}

//@ predicate student(char *name;) = string(name, ?cs) &*& malloc_block_chars(name, length(cs) + 1);

int main() //@ : main
    //@ requires true;
    //@ ensures true;
{
    printf("How many students do you have? ");
    int n = read_int();
    if (n < 0 || 0x20000000 <= n) abort();
    char **names = malloc(n * sizeof(char *));
    if (names == 0) abort();
    for (int i = 0; ; i++)
        //@ requires names[i..n] |-> _;
        //@ ensures names[old_i..n] |-> ?ps &*& foreachp(ps, student);
    {
        //@ open pointers_(_, _, _);
        if (i == n) {
            break;
        }
        printf("Please enter the name of student number %d: ", i + 1);
        char *name = read_line();
        printf("Adding '%s'...\n", name);
        names[i] = name;
    }
    
    for (;;)
        //@ invariant names[0..n] |-> ?ps &*& foreachp(ps, student);
    {
        printf("Please enter a student number: ");
        int k = read_int();
        if (k < 1 || n < k) {
            printf("Student number out of range. Terminating...\n");
            break;
        } else {
            char *name = names[k - 1];
            //@ foreachp_remove_nth(k - 1);
            printf("Student number %d is called %s.\n", k, name);
            //@ foreachp_unremove_nth(ps, k - 1);
        }
    }
    
    for (int i = 0; ; i++)
        //@ requires names[i..n] |-> ?ps &*& foreachp(ps, student);
        //@ ensures names[old_i..n] |-> _;
    {
        //@ open pointers(_, _, _);
        if (i == n) {
            break;
        }
        //@ open foreachp(_, _);
        //@ string_to_chars(names[i]);
        free(names[i]);
    }
    free(names);
    
    return 0;
}