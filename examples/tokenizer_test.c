#include <stdio.h>
#include "tokenizer.h"

int my_getchar() //@ : charreader
	//@ requires true;
	//@ ensures true;
{
	return getchar();
}

int main()
 //@ requires true;
 //@ ensures true;
{
	struct tokenizer* tokenizer = tokenizer_create(my_getchar);

	for (;;)
		//@ invariant Tokenizer(tokenizer);
	{
		int result = tokenizer_next(tokenizer);
		if (result == -1) break;
		print_token(tokenizer);
	}
	
	tokenizer_dispose(tokenizer);

	puts("The end");
	return 0;
}
