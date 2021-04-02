#include <stdint.h>

struct x {
	uint64_t a;
	uint64_t b;
};

void foo(void)
//@ requires emp;
//@ ensures emp;
{
	//@ assert sizeof(struct x) >= 0;
	//@ assert sizeof(struct x) <= SIZE_MAX;

	// The compiler can add alignment or padding, so this may not be true
	//@ assert sizeof(struct x) == 16; //~ should_fail
}
