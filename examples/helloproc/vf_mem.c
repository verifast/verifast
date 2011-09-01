#include "vf_mem.h"
#include <asm/uaccess.h>
#include <linux/slab.h>

/*
 * Allocating 0 bytes is allowed in Linux, search for ZERO_SIZE_PTR in
 * slab.h in Linux (starting from 2.6.22).
 *
 * I can't find any official specs/documentation that approves
 * memcpy'ing 0 bytes (memcpy in kernel, not the userspace memcpy).
 * lib/string.c implicitly supports it, __constant_memcpy in
 * arch/x86/include/asm/string_32.h supports it explicitly, so we
 * might think that *probably* memcpy'ing 0 bytes is allowed.
 * However, as long as we are not entirely sure, we can not allow it
 * in the API implementation here.  Since the vf_API specification
 * disallows it too, we don't have to check anything though.
 *
 * memcpy does not support overlap (not documented at memcpy itself
 * but it is documented at memmove in lib/string.c).
 */


void vf_kfree(void *ptr)
{
	kfree(ptr);
}


void *vf_kmalloc(int size)
{
	return kmalloc(size, GFP_KERNEL);
}


void *vf_kzalloc(int size)
{
	return kzalloc(size, GFP_KERNEL);
}


void vf_memcpy(void *dest, void *src, int count)
{
	memcpy(dest, src, count);
}


int vf_copy_from_user(void *to, void *from, int count)
{
	return copy_from_user(to, from, (long)count);
}
