#include "stdio.h"
#include "stdlib.h"
#include "tokenizer.h"

struct tokenizer
{
	charreader*           next_char;
	int                   lastread; // -1 = EOF, -2 = empty buffer
	int                   lasttoken;
	struct string_buffer* buffer;
};

/*@

predicate Tokenizer(struct tokenizer* t;) =
  malloc_block_tokenizer(t) &*&
  t->next_char |-> ?nc &*& is_charreader(nc) == true &*&
  t->lastread |-> ?lastread &*&
  t->lasttoken |-> ?lasttoken &*&
  t->buffer |-> ?b &*& string_buffer(b, _);

predicate Tokenizer_minus_buffer(struct tokenizer* t; struct string_buffer *buffer) =
  malloc_block_tokenizer(t) &*&
  t->next_char |-> ?nc &*& is_charreader(nc) == true &*&
  t->lastread |-> ?lastread &*&
  t->lasttoken |-> ?lasttoken &*&
  t->buffer |-> buffer;

lemma void tokenizer_merge_buffer(struct tokenizer *tokenizer)
    requires Tokenizer_minus_buffer(tokenizer, ?buffer) &*& string_buffer(buffer, _);
    ensures Tokenizer(tokenizer);
{
    close Tokenizer(tokenizer);
}

@*/

void tokenizer_fill_buffer(struct tokenizer* tokenizer)
 //@ requires Tokenizer(tokenizer);
 //@ ensures Tokenizer(tokenizer);
{
	if ( tokenizer->lastread == -2 )
	{
	        charreader *reader = tokenizer->next_char;
	        int result = reader();
		tokenizer->lastread = result;
	}
}

int tokenizer_peek(struct tokenizer* tokenizer)
 //@ requires Tokenizer(tokenizer);
 //@ ensures Tokenizer(tokenizer);
{
	tokenizer_fill_buffer(tokenizer);
	return tokenizer->lastread;
}

void tokenizer_drop(struct tokenizer* tokenizer)
 //@ requires Tokenizer(tokenizer);
 //@ ensures Tokenizer(tokenizer);
{
	tokenizer->lastread = -2;
}

int tokenizer_next_char(struct tokenizer* tokenizer)
 //@ requires Tokenizer(tokenizer);
 //@ ensures Tokenizer(tokenizer);
{
	int c;

	tokenizer_fill_buffer(tokenizer);
	c = tokenizer->lastread;
	tokenizer->lastread = -2;
	return c;
}

bool is_whitespace(int c)
 //@ requires true;
 //@ ensures true;
{
	return c == ' ' || c == '\n' || c == '\r' || c == '\t';
}

void tokenizer_skip_whitespace(struct tokenizer* tokenizer)
 //@ requires Tokenizer(tokenizer);
 //@ ensures Tokenizer(tokenizer);
{
	while ( is_whitespace( tokenizer_peek(tokenizer) ) )
		//@ invariant Tokenizer(tokenizer);
	{
		tokenizer_drop(tokenizer);
	}
}

bool is_digit(int c)
 //@ requires true;
 //@ ensures true;
{
	return c >= '0' && c <= '9';
}

void string_buffer_append_char(struct string_buffer *buffer, char c)
 //@ requires string_buffer(buffer, _);
 //@ ensures string_buffer(buffer, _);
{
	char cc = c;
	string_buffer_append_chars(buffer, &cc, 1);
}

int tokenizer_eat_number(struct tokenizer* tokenizer)
 //@ requires Tokenizer(tokenizer);
 //@ ensures Tokenizer(tokenizer);
{
	for (;;)
	  //@ invariant Tokenizer(tokenizer);
	{
		int result;
		bool isDigit;
		
		result = tokenizer_peek(tokenizer);
		isDigit = is_digit(result);
		if ( !isDigit ) break;
		
	        result = tokenizer_next_char(tokenizer);
		string_buffer_append_char(tokenizer->buffer, (char)result);
	}

	return '0';
}

bool is_symbol_char(int c)
 //@ requires true;
 //@ ensures true;
{
	return c > 32 && c <= 127 && c != '(' && c != ')'; 
}

int tokenizer_eat_symbol(struct tokenizer* tokenizer)
 //@ requires Tokenizer(tokenizer);
 //@ ensures Tokenizer(tokenizer);
{
	for (;;)
		//@ invariant Tokenizer(tokenizer);
	{
		int result;
		bool isSymbolChar;
		
		result = tokenizer_peek(tokenizer);
		isSymbolChar = is_symbol_char(result);
		
		if (!isSymbolChar) break;
		
		result = tokenizer_next_char(tokenizer);
		string_buffer_append_char(tokenizer->buffer, (char)result);
	}

	return 'S';
}

int tokenizer_next(struct tokenizer* tokenizer)
 //@ requires Tokenizer(tokenizer);
 //@ ensures Tokenizer(tokenizer);
{
	int c;
	int token;

	string_buffer_clear(tokenizer->buffer);
	tokenizer_skip_whitespace(tokenizer);

	c = tokenizer_peek(tokenizer);

	if ( c == '(' || c == ')' || c == -1 )
	{
		tokenizer_drop(tokenizer);
		token = c;
	}
	else if ( is_digit(c) )
	{
		
		token = tokenizer_eat_number(tokenizer);
	}
	else if ( is_symbol_char(c) )
	{
		token = tokenizer_eat_symbol(tokenizer);
	}
	else
	{
		tokenizer_drop(tokenizer);
		token = 'B'; // bad character
	}
	tokenizer->lasttoken = token;
	return token;
}

struct string_buffer *tokenizer_get_buffer(struct tokenizer *tokenizer)
    //@ requires Tokenizer(tokenizer);
    //@ ensures Tokenizer_minus_buffer(tokenizer, result) &*& string_buffer(result, _);
{
    return tokenizer->buffer;
    //@ close Tokenizer_minus_buffer(tokenizer, tokenizer->buffer);
}

struct tokenizer* tokenizer_create(charreader* reader)
 //@ requires is_charreader(reader) == true;
 //@ ensures Tokenizer(result);
{
	struct tokenizer* tokenizer;
	struct string_buffer *buffer;
	
	tokenizer = (struct tokenizer*) malloc( sizeof( struct tokenizer ) );
	if ( tokenizer == 0 ) abort();
	tokenizer->lastread = -2;
	tokenizer->lasttoken = 0;
	tokenizer->next_char = reader;
	buffer = create_string_buffer();
	tokenizer->buffer = buffer;
	return tokenizer;
}

void tokenizer_dispose(struct tokenizer *tokenizer)
	//@ requires Tokenizer(tokenizer);
	//@ ensures true;
{
	string_buffer_dispose(tokenizer->buffer);
	free(tokenizer);
}

void print_string_buffer(struct string_buffer *buffer)
	//@ requires [?f]string_buffer(buffer, ?cs);
	//@ ensures [f]string_buffer(buffer, cs);
{
	int n = string_buffer_get_length(buffer);
	char *pcs = string_buffer_get_chars(buffer);
	int i;
	for (i = 0; i < n; i++)
		//@ invariant [f]pcs[0..n] |-> cs &*& 0 <= i;
	{
		putchar(pcs[i]);
	}
	//@ string_buffer_merge_chars(buffer);
}

void print_token(struct tokenizer* tokenizer)
 //@ requires Tokenizer(tokenizer);
 //@ ensures Tokenizer(tokenizer);
{
	switch ( tokenizer->lasttoken )
	{
	case '(':
		puts("LPAREN");
		break;

	case ')':
		puts("RPAREN");
		break;

	case '0':
		putchar('N');
		print_string_buffer(tokenizer->buffer);
		puts("");
		break;

	case 'S':
		putchar('S');
		print_string_buffer(tokenizer->buffer);
		puts("");
		break;
	
	case 'B':
		puts("BADCHAR");
		break;
	}
}
