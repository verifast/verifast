#include <stdint.h>

struct foo {
	int64_t bar;
	uint64_t ubar;
};

void test(struct foo *f)
	//@ requires foo_bar(f, _) &*& foo_ubar(f, _);
	//@ ensures *&f->bar |-> _ &*& *&f->ubar |-> _;
{
}
