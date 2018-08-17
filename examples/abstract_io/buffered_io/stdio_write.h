#ifndef STDIO_WRITE_H
#define STDIO_WRITE_H

#include "write.h"
#include "stdio.h"

/*@

predicate stdout_buffer(; list<char> cs);

predicate stdout_buffer_token(list<char> cs, predicate() Q) =
    stdout_buffer(cs) &*& token(?P) &*& write_chars_(P, cs, Q);

predicate_ctor unspec_stdout_buffer_token(predicate() Q)() = stdout_buffer_token(_, Q);

predicate putchar_(predicate() P, char c, predicate() Q) =
    write_char_(?Plow, c, ?Qlow) &*&
    conseq(P, unspec_stdout_buffer_token(Plow), unspec_stdout_buffer_token(Qlow), Q);

lemma void putchar__intro();
    requires write_char_(?P, ?c, ?Q);
    ensures putchar_(unspec_stdout_buffer_token(P), c, unspec_stdout_buffer_token(Q));

predicate_ctor empty_stdout_buffer_token(predicate() Q)() = stdout_buffer_token(nil, Q);

lemma void empty_stdout_buffer_token_elim(predicate() P);
    requires token(empty_stdout_buffer_token(P));
    ensures stdout_buffer(nil) &*& token(P);

predicate flush_(predicate() P, predicate() Q) =
    exists<predicate()>(?Qlow) &*&
    conseq(P, unspec_stdout_buffer_token(Qlow), empty_stdout_buffer_token(Qlow), Q);

lemma void flush__intro(predicate() Qlow);
    requires true;
    ensures flush_(unspec_stdout_buffer_token(Qlow), empty_stdout_buffer_token(Qlow));

require_module stdio;

lemma void stdio_init();
    requires module(stdio, true);
    ensures stdout_buffer(nil);

lemma void destroy_stdio();
    requires stdout_buffer(_);
    ensures module(stdio, false);

@*/

#endif
