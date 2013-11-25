#ifndef _LINUX_TYPES_H
#define _LINUX_TYPES_H

typedef unsigned int    __kernel_size_t; // We verify for x86-32.
typedef __kernel_size_t         size_t;

#define __bitwise__ 

typedef int dma_addr_t;


// Note: architecture-dependent.
typedef unsigned char __u8;
typedef short __le16; // XXX yes? short?
typedef short __u16;

#endif