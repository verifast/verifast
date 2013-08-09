#ifndef _LINUX_TYPES_H
#define _LINUX_TYPES_H

// XXX This should be unsigned, but then we need to have lots of annoying casts in VeriFast.
// UNSAFE I'm not convinced this is sound (combined with C's auto-casting).
//        Todo: Replace this with an explanation why it is sound, or fix the unsoundness.
typedef /*unsigned*/ int    __kernel_size_t; // We verify for x86-32.
typedef __kernel_size_t         size_t;

#define __bitwise__ 

typedef int dma_addr_t;


// Note: architecture-dependent.
typedef unsigned char __u8;
typedef short __le16; // XXX yes? short?
typedef short __u16;

#endif