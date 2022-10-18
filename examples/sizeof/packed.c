#include <stdint.h>
#include <stdlib.h>

struct x {
	uint64_t a;
	uint8_t b;
} __attribute__((packed));

struct y {
	struct x value;
};

void foo(void)
//@ requires emp;
//@ ensures emp;
{
	// Proper size
	//@ assert sizeof(struct x) == 9;

	// No offset inside
	struct x value;
	//@ assert (char*) &(value.b) == (char*) &value + sizeof(uint64_t);

	// No padding
	struct y* allocated = malloc(sizeof(struct y));
	if (allocated != NULL) {
		//@ leak malloc_block_y(allocated);
		//@ leak x_a_(&(allocated->value), _);
		//@ leak x_b_(&(allocated->value), _);
	}
}
