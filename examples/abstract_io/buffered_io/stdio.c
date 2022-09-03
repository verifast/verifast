#include "stdio_write.h"

#define BUFFER_SIZE 100
char buffer[BUFFER_SIZE];
int count;

/*@

lemma void putchar__weaken()
    requires putchar_(?P2, ?c, ?Q1) &*& conseq(?P1, P2, Q1, ?Q2);
    ensures putchar_(P1, c, Q2);
{
    open putchar_(P2, c, Q1);
    conseq_trans(P1);
    close putchar_(P1, c, Q2);
}

lemma void flush__weaken()
    requires flush_(?P2, ?Q1) &*& conseq(?P1, P2, Q1, ?Q2);
    ensures flush_(P1, Q2);
{
    open flush_(P2, Q1);
    conseq_trans(P1);
    close flush_(P1, Q2);
}

predicate stdout_buffer(; list<char> cs) =
    count |-> ?n &*& buffer[..n] |-> cs &*& buffer[n..BUFFER_SIZE] |-> _ &*& n < BUFFER_SIZE;

lemma void putchar__intro()
    requires write_char_(?P, ?c, ?Q);
    ensures putchar_(unspec_stdout_buffer_token(P), c, unspec_stdout_buffer_token(Q));
{
    conseq_refl(unspec_stdout_buffer_token(P), unspec_stdout_buffer_token(Q));
    close putchar_(unspec_stdout_buffer_token(P), c, unspec_stdout_buffer_token(Q));
}

lemma void flush__intro(predicate() Qlow)
    requires true;
    ensures flush_(unspec_stdout_buffer_token(Qlow), empty_stdout_buffer_token(Qlow));
{
    close exists(Qlow);
    conseq_refl(unspec_stdout_buffer_token(Qlow), empty_stdout_buffer_token(Qlow));
    close flush_(unspec_stdout_buffer_token(Qlow), empty_stdout_buffer_token(Qlow));
}

lemma void empty_stdout_buffer_token_elim(predicate() P)
    requires token(empty_stdout_buffer_token(P));
    ensures stdout_buffer(nil) &*& token(P);
{
    open token(empty_stdout_buffer_token(P));
    open empty_stdout_buffer_token(P)();
    open stdout_buffer_token(nil, P);
    open token(?P0);
    open write_chars_(P0, nil, P);
    modus_ponens();
    close token(P);
}

lemma void stdio_init()
    requires module(stdio, true);
    ensures stdout_buffer(nil);
{
    open_module();
    close stdout_buffer(nil);
}

lemma void destroy_stdio()
    requires stdout_buffer(_);
    ensures module(stdio, false);
{
    open stdout_buffer(_);
    close_module();
}

@*/

void putchar_core(char c)
    //@ requires stdout_buffer_token(_, ?Q) &*& write_char_(Q, c, ?R);
    //@ ensures stdout_buffer_token(_, R);
{
    //@ open stdout_buffer_token(_, _);
    //@ open stdout_buffer(_);
    buffer[count] = c;
    //@ close chars((char *)buffer + count, 1, _);
    //@ chars_join(buffer);
    //@ write_chars__add();
    count++;
    if (count == BUFFER_SIZE) {
        write_stdout(buffer, BUFFER_SIZE);
        count = 0;
        //@ implies_refl(R, True);
        //@ close write_chars_(R, nil, R);
    }
    //@ close stdout_buffer(_);
    //@ close stdout_buffer_token(_, R);
}

void putchar(char c)
    //@ requires token(?P) &*& putchar_(P, c, ?Q);
    //@ ensures token(Q);
{
    //@ open putchar_(P, c, Q);
    //@ conseq_elim();
    //@ assert write_char_(?Plow, c, ?Qlow);
    //@ open unspec_stdout_buffer_token(Plow)();
    putchar_core(c);
    //@ close unspec_stdout_buffer_token(Qlow)();
    //@ modus_ponens();
    //@ close token(Q);
}

void flush_core()
    //@ requires stdout_buffer_token(_, ?Q);
    //@ ensures stdout_buffer_token(nil, Q);
{
    //@ open stdout_buffer_token(_, _);
    //@ open stdout_buffer(_);
    write_stdout(buffer, count);
    count = 0;
    //@ close stdout_buffer(nil);
    //@ produce_lemma_function_pointer_chunk implies(Q, True, Q, True)() {};
    //@ close write_chars_(Q, nil, Q);
    //@ close stdout_buffer_token(nil, Q);
}

void flush()
    //@ requires token(?P) &*& flush_(P, ?Q);
    //@ ensures token(Q);
{
    //@ open flush_(P, Q);
    //@ open exists(?Qlow);
    //@ conseq_elim();
    //@ open unspec_stdout_buffer_token(Qlow)();
    flush_core();
    //@ close empty_stdout_buffer_token(Qlow)();
    //@ modus_ponens();
    //@ close token(Q);
}
