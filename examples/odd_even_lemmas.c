// This contrived example is not useful in any way; it just shows that you can do mutual lemma recursion using lemma function pointer chunks.

/*@

typedef lemma void oddfunc(oddfunc *odd, evenfunc *even, int x);
    requires multi_is_oddfunc(odd, x) &*& multi_is_evenfunc(even, x);
    ensures true;

typedef lemma void evenfunc(oddfunc *odd, evenfunc *even, int x);
    requires multi_is_oddfunc(odd, x) &*& multi_is_evenfunc(even, x);
    ensures true;

predicate multi_is_oddfunc(oddfunc *odd, int n) = n <= 0 ? emp : is_oddfunc(odd) &*& multi_is_oddfunc(odd, n - 1);
predicate multi_is_evenfunc(evenfunc *even, int n) = n <= 0 ? emp : is_evenfunc(even) &*& multi_is_evenfunc(even, n - 1);

lemma void odd_lemma(oddfunc *odd, evenfunc *even, int x) : oddfunc
    requires multi_is_oddfunc(odd, x) &*& multi_is_evenfunc(even, x);
    ensures true;
{
    open multi_is_oddfunc(odd, x);
    open multi_is_evenfunc(even, x);
    if (x <= 0) {
    } else {
        even(odd, even, x - 1);
        leak is_oddfunc(odd);
        leak is_evenfunc(even);
    }
}

lemma void even_lemma(oddfunc *odd, evenfunc *even, int x) : evenfunc
    requires multi_is_oddfunc(odd, x) &*& multi_is_evenfunc(even, x);
    ensures true;
{
    open multi_is_oddfunc(odd, x);
    open multi_is_evenfunc(even, x);
    if (x <= 0) {
    } else {
        odd(odd, even, x - 1);
        leak is_oddfunc(odd);
        leak is_evenfunc(even);
    }
}

inductive nat = zero | succ(nat);

fixpoint int int_of_nat(nat n) {
    switch (n) {
        case zero: return 0;
        case succ(m): return 1 + int_of_nat(m);
    }
}

lemma void int_of_nat_nonneg(nat n)
    requires true;
    ensures 0 <= int_of_nat(n);
{
    switch (n) {
        case zero:
        case succ(m):
            int_of_nat_nonneg(m);
    }
}

lemma void produce_multi_is_oddfunc(nat n)
    requires true;
    ensures multi_is_oddfunc(odd_lemma, int_of_nat(n));
{
    switch (n) {
        case zero: 
            close multi_is_oddfunc(odd_lemma, int_of_nat(n));
        case succ(m):
            int_of_nat_nonneg(m);
            produce_lemma_function_pointer_chunk(odd_lemma);
            produce_multi_is_oddfunc(m);
            close multi_is_oddfunc(odd_lemma, int_of_nat(n));
    }
}

lemma void produce_multi_is_evenfunc(nat n)
    requires true;
    ensures multi_is_evenfunc(even_lemma, int_of_nat(n));
{
    switch (n) {
        case zero: 
            close multi_is_evenfunc(even_lemma, int_of_nat(n));
        case succ(m):
            int_of_nat_nonneg(m);
            produce_lemma_function_pointer_chunk(even_lemma);
            produce_multi_is_evenfunc(m);
            close multi_is_evenfunc(even_lemma, int_of_nat(n));
    }
}

lemma void main_lemma(nat n)
    requires true;
    ensures true;
{
    produce_multi_is_oddfunc(n);
    produce_multi_is_evenfunc(n);
    odd_lemma(odd_lemma, even_lemma, int_of_nat(n));
}

@*/