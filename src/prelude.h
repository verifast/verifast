#ifndef PRELUDE_H
#define PRELUDE_H

/*@

inductive unit = unit;

inductive boxed_int = boxed_int(int);
fixpoint int unboxed_int(boxed_int i) { switch (i) { case boxed_int(value): return value; } }

inductive boxed_bool = boxed_bool(bool);
fixpoint bool unboxed_bool(boxed_bool b) { switch (b) { case boxed_bool(value): return value; } }

inductive boxed_real = boxed_real(real);
fixpoint real unboxed_real(boxed_real r) { switch (r) { case boxed_real(value): return value; } }

inductive chars = chars_nil | chars_cons(char, chars);

fixpoint int chars_length(chars cs) {
    switch (cs) {
        case chars_nil: return 0;
        case chars_cons(c, cs0): return 1 + chars_length(cs0);
    }
}

fixpoint chars chars_take(chars cs, int offset) {
    switch (cs) {
        case chars_nil: return chars_nil;
        case chars_cons(c, cs0): return offset == 0 ? chars_nil : chars_cons(c, chars_take(cs0, offset - 1));
    }
}

fixpoint chars chars_drop(chars cs, int offset) {
    switch (cs) {
        case chars_nil: return chars_nil;
        case chars_cons(c, cs0): return offset == 0 ? cs : chars_drop(cs0, offset - 1);
    }
}

fixpoint bool chars_contains(chars cs, char c) {
    switch (cs) {
        case chars_nil: return false;
        case chars_cons(c0, cs0): return c0 == c || chars_contains(cs0, c);
    }
}

fixpoint int chars_index_of(chars cs, char c) {
    switch (cs) {
        case chars_nil: return -1;
        case chars_cons(c0, cs0): return c0 == c ? 0 : 1 + chars_index_of(cs0, c);
    }
}

fixpoint chars chars_append(chars cs, chars cs0) {
    switch (cs) {
        case chars_nil: return cs0;
        case chars_cons(c, cs1): return chars_cons(c, chars_append(cs1, cs0));
    }
}

lemma void chars_length_nonnegative(chars cs);
    requires true;
    ensures 0 <= chars_length(cs);

lemma void chars_contains_chars_index_of(chars cs, char c);
    requires true;
    ensures chars_contains(cs, c) == (0 <= chars_index_of(cs, c) && chars_index_of(cs, c) <= chars_length(cs));

predicate chars(char *array, chars cs);

predicate string_literal(char *array, chars cs);

lemma void chars_nil(char *array);
    requires emp;
    ensures chars(array, chars_nil);

lemma void open_chars_nil(char *array);
    requires chars(array, chars_nil);
    ensures emp;

lemma void chars_split(char *array, int offset);
   requires [?f]chars(array, ?cs) &*& 0 <= offset &*& offset <= chars_length(cs);
   ensures
       [f]chars(array, chars_take(cs, offset))
       &*& [f]chars(array + chars_length(chars_take(cs, offset)), chars_drop(cs, offset))
       &*& chars_length(chars_take(cs, offset)) == offset
       &*& chars_length(chars_drop(cs, offset)) == chars_length(cs) - offset
       &*& chars_append(chars_take(cs, offset), chars_drop(cs, offset)) == cs;

lemma void chars_join(char *array);
    requires [?f]chars(array, ?cs) &*& [f]chars(array + chars_length(cs), ?cs0);
    ensures
        [f]chars(array, chars_append(cs, cs0))
        &*& chars_length(chars_append(cs, cs0)) == chars_length(cs) + chars_length(cs0); // To avoid lemma call at call site in common scenario.

lemma void assume(bool b);
    requires true;
    ensures b;

predicate integer(int *p; int v);

lemma void chars_to_integer(void *p);
    requires chars(p, ?cs) &*& chars_length(cs) == 4;
    ensures integer(p, _);

lemma void integer_to_chars(void *p);
    requires integer(p, _);
    ensures chars(p, ?cs) &*& chars_length(cs) == 4;

predicate pointer(void **pp; void *p);

lemma void chars_to_pointer(void *p);
    requires chars(p, ?cs) &*& chars_length(cs) == 4;
    ensures pointer(p, _);

lemma void pointer_to_chars(void *p);
    requires pointer(p, _);
    ensures chars(p, ?cs) &*& chars_length(cs) == 4;

@*/

int main();
    //@ requires emp;
    //@ ensures emp;

#endif