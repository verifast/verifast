// This contrived example is not useful in any way; it just shows that you can do mutual lemma recursion using lemma function pointer chunks.

/*@

typedef lemma void oddfunc(oddfunc *odd, evenfunc *even, int x);
    requires multi_is_oddfunc(odd, x) &*& multi_is_evenfunc(even, x);
    ensures multi_is_oddfunc(odd, x) &*& multi_is_evenfunc(even, x);

typedef lemma void evenfunc(oddfunc *odd, evenfunc *even, int x);
    requires multi_is_oddfunc(odd, x) &*& multi_is_evenfunc(even, x);
    ensures multi_is_oddfunc(odd, x) &*& multi_is_evenfunc(even, x);

predicate multi_is_oddfunc(oddfunc *odd, int n) = n <= 0 ? emp : is_oddfunc(odd) &*& multi_is_oddfunc(odd, n - 1);
predicate multi_is_evenfunc(evenfunc *even, int n) = n <= 0 ? emp : is_evenfunc(even) &*& multi_is_evenfunc(even, n - 1);

lemma void odd_lemma(oddfunc *odd, evenfunc *even, int x) : oddfunc
    requires multi_is_oddfunc(odd, x) &*& multi_is_evenfunc(even, x);
    ensures multi_is_oddfunc(odd, x) &*& multi_is_evenfunc(even, x);
{
    open multi_is_oddfunc(odd, x);
    open multi_is_evenfunc(even, x);
    if (x <= 0) {
    } else {
        even(odd, even, x - 1);
    }
    close multi_is_oddfunc(odd, x);
    close multi_is_evenfunc(even, x);
}

lemma void even_lemma(oddfunc *odd, evenfunc *even, int x) : evenfunc
    requires multi_is_oddfunc(odd, x) &*& multi_is_evenfunc(even, x);
    ensures multi_is_oddfunc(odd, x) &*& multi_is_evenfunc(even, x);
{
    open multi_is_oddfunc(odd, x);
    open multi_is_evenfunc(even, x);
    if (x <= 0) {
    } else {
        odd(odd, even, x - 1);
    }
    close multi_is_oddfunc(odd, x);
    close multi_is_evenfunc(even, x);
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

lemma void produce_chunks(int m, nat n)
    requires multi_is_oddfunc(odd_lemma, m - int_of_nat(n)) &*& multi_is_evenfunc(even_lemma, m - int_of_nat(n));
    ensures multi_is_oddfunc(odd_lemma, m - int_of_nat(n)) &*& multi_is_evenfunc(even_lemma, m - int_of_nat(n));
{
    switch (n) {
        case zero: 
            odd_lemma(odd_lemma, even_lemma, m);
        case succ(n0):
            int_of_nat_nonneg(n0);
            produce_lemma_function_pointer_chunk(odd_lemma) {
              produce_lemma_function_pointer_chunk(even_lemma) {
                close multi_is_oddfunc(odd_lemma, m - int_of_nat(n0));
                close multi_is_evenfunc(even_lemma, m - int_of_nat(n0));
                produce_chunks(m, n0);
                open multi_is_oddfunc(odd_lemma, m - int_of_nat(n0));
                open multi_is_evenfunc(even_lemma, m - int_of_nat(n0));
              }
            }
    }
}
lemma void main_lemma(nat n)
    requires true;
    ensures true;
{
    close multi_is_evenfunc(even_lemma, 0);
    close multi_is_oddfunc(odd_lemma, 0);
    produce_chunks(int_of_nat(n), n);
    open multi_is_evenfunc(even_lemma, 0);
    open multi_is_oddfunc(odd_lemma, 0);
}

@*/