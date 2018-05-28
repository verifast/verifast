#ifndef PRELUDE_H
#define PRELUDE_H

/*@

inductive list<t> = nil | cons(t, list<t>);

fixpoint int length<t>(list<t> xs) {
    switch (xs) {
        case nil: return 0;
        case cons(x, xs0): return 1 + length(xs0);
    }
}

predicate custom_chars(char *arr, int size, list<char> cs);

lemma_auto void custom_chars_inv();
    requires [?f]custom_chars(?arr, ?count, ?cs);
    ensures [f]custom_chars(arr, count, cs) &*& length(cs) == count;

predicate malloc_block(void *p; int size);

@*/

typedef int main();
    //@ requires true;
    //@ ensures true;

#endif
