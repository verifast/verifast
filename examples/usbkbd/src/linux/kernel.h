#ifndef _LINUX_KERNEL_H
#define _LINUX_KERNEL_H

#include <linux/printk.h>
#include <linux/stddef.h>
#include <linux/spinlock.h> // XXX not directly included from here, should look up the include path.

// XXX I don't know what the include path is until linux/string.h
// is included, so we just include it here for now.
#include "string.h"

// XXX should be in another file
//
// Comes from asm-generic/bitops/non-atomic.h
// It is not atomic!
int test_bit (int nr, const /*volatile*/ void *addr);
/*@ requires
	[?f]chars(addr, ?length, ?cs)
	&*& length * 8 > nr;
@*/
//@ ensures [f]chars(addr, length, cs);

// XXX shouldn't be here.
void set_bit(int nr, /*unsigned long*/ int *addr); // XXX ??? why unsigned long?
/*@ requires
	ints(addr,?length, ?contents)
	&*& nr < length * sizeof(int) * 8;
@*/
//@ ensures ints(addr,length,?new_contents);

// XXX clear_bit is actually from asm-generic/bitops/atomic.h (which is not in linux/)
void clear_bit(int nr, /*volatile unsigned long*/ int *addr); // XXX unsigned long pointer thing
/*@ requires
	ints(addr, ?length, ?contents)
	&*& nr < length * sizeof(int) * 8;
@*/
//@ ensures ints(addr,length,?new_contents);

// This is actually a macro.
// XXX should  be in bitops.h
// XXX should be unsigned longs.
// XXX no precondition?
int BIT_MASK(int nr);
//@ requires true;
//@ ensures true;

__le16 cpu_to_le16(int x);
//@ requires true;
//@ ensures true;

#endif
