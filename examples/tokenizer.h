#ifndef TOKENIZER_H
#define TOKENIZER_H

#include "stringBuffers.h"
//@ #include "arrays.gh"

typedef int charreader();
    //@ requires true;
    //@ ensures true;

struct tokenizer;

//@ predicate Tokenizer(struct tokenizer* t;);



struct tokenizer* tokenizer_create(charreader* reader);
    //@ requires is_charreader(reader) == true;
    //@ ensures Tokenizer(result);

void tokenizer_dispose(struct tokenizer *tokenizer);
    //@ requires Tokenizer(tokenizer);
    //@ ensures true;

struct string_buffer *tokenizer_get_buffer(struct tokenizer *tokenizer);
    //@ requires Tokenizer(tokenizer);
    //@ ensures Tokenizer_minus_buffer(tokenizer, result) &*& string_buffer(result, _);

/*@

predicate Tokenizer_minus_buffer(struct tokenizer *tokenizer; struct string_buffer *buffer);

lemma void tokenizer_merge_buffer(struct tokenizer *tokenizer);
    requires Tokenizer_minus_buffer(tokenizer, ?buffer) &*& string_buffer(buffer, _);
    ensures Tokenizer(tokenizer);

@*/

int tokenizer_next(struct tokenizer* tokenizer);
    //@ requires Tokenizer(tokenizer);
    //@ ensures Tokenizer(tokenizer);

void print_string_buffer(struct string_buffer *buffer);
    //@ requires [?f]string_buffer(buffer, ?cs);
    //@ ensures [f]string_buffer(buffer, cs);

void print_token(struct tokenizer* tokenizer);
    //@ requires Tokenizer(tokenizer);
    //@ ensures Tokenizer(tokenizer);

#endif