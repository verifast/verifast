#ifndef PRELUDE_H
#define PRELUDE_H

#include "prelude_core.h"
#include "list.h"

/*@

lemma void assume(bool b);
    requires true;
    ensures b;

@*/

/*@

predicate character(char *p; char c);

predicate integer(int *p; int v);

predicate pointer(void **pp; void *p);

lemma void pointer_distinct(void *pp1, void *pp2);
    requires pointer(pp1, ?p1) &*& pointer(pp2, ?p2);
    ensures pointer(pp1, p1) &*& pointer(pp2, p2) &*& pp1 != pp2;

lemma void pointer_unique(void *pp);
    requires [?f]pointer(pp, ?p);
    ensures [f]pointer(pp, p) &*& f <= 1;

lemma void pointer_nonzero(void *pp);
    requires pointer(pp, ?p);
    ensures pointer(pp, p) &*& pp != 0;

fixpoint void *pointer_of_chars(list<char> cs);
fixpoint list<char> chars_of_pointer(void * p);
fixpoint bool chars_within_limits(list<char> cs);

lemma void pointer_of_chars_of_pointer(void *p);
    requires p >= (void *)0 &*& p <= (void *)UINTPTR_MAX;
    ensures pointer_of_chars(chars_of_pointer(p)) == p &*& chars_within_limits(chars_of_pointer(p)) == true &*& length(chars_of_pointer(p)) == sizeof(void *);

lemma void chars_of_pointer_of_chars(list<char> cs);
    requires length(cs) == sizeof(void *) &*& chars_within_limits(cs) == true;
    ensures chars_of_pointer(pointer_of_chars(cs)) == cs;

@*/

/*@

predicate chars(char *array, list<char> cs) =
    switch (cs) {
        case nil: return true;
        case cons(c, cs0): return character(array, c) &*& chars(array + 1, cs0);
    };

lemma void chars_zero(); // There is nothing at address 0.
    requires chars(0, ?cs);
    ensures cs == nil;

lemma void chars_limits(char *array);
    requires [?f]chars(array, ?cs);
    ensures [f]chars(array, cs) &*& cs == nil ? true : true == ((char *)0 <= array) &*& array + length(cs) <= (char *)UINTPTR_MAX;

lemma void chars_split(char *array, int offset);
   requires [?f]chars(array, ?cs) &*& 0 <= offset &*& offset <= length(cs);
   ensures
       [f]chars(array, take(offset, cs))
       &*& [f]chars(array + length(take(offset, cs)), drop(offset, cs))
       &*& length(take(offset, cs)) == offset
       &*& length(drop(offset, cs)) == length(cs) - offset
       &*& append(take(offset, cs), drop(offset, cs)) == cs;

lemma void chars_join(char *array);
    requires [?f]chars(array, ?cs) &*& [f]chars(array + length(cs), ?cs0);
    ensures
        [f]chars(array, append(cs, cs0))
        &*& length(append(cs, cs0)) == length(cs) + length(cs0); // To avoid lemma call at call site in common scenario.

lemma void chars_to_integer(void *p);
    requires chars(p, ?cs) &*& length(cs) == sizeof(int);
    ensures integer(p, _);

lemma void integer_to_chars(void *p);
    requires integer(p, _);
    ensures chars(p, ?cs) &*& length(cs) == sizeof(int);

lemma void chars_to_pointer(void *p);
    requires chars(p, ?cs) &*& length(cs) == sizeof(void *);
    ensures pointer(p, pointer_of_chars(cs));

lemma void pointer_to_chars(void *p);
    requires pointer(p, ?v);
    ensures chars(p, chars_of_pointer(v)) &*& length(chars_of_pointer(v)) == sizeof(void *);

@*/

/*@

predicate module(int moduleId, bool initialState);
predicate module_code(int moduleId;);

predicate char_array(char **a, int count) =
    count <= 0 ? true : pointer(a, ?c) &*& chars(c, ?cs) &*& mem('\0', cs) == true &*& char_array(a + 1, count - 1);

@*/

typedef int main(int argc, char **argv);
    //@ requires 0 <= argc &*& [_]char_array(argv, argc);
    //@ ensures true;

typedef int main_full/*@(int mainModule)@*/(int argc, char **argv);
    //@ requires module(mainModule, true) &*& [_]char_array(argv, argc);
    //@ ensures true;

#endif