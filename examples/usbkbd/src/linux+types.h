#ifndef _LINUX_TYPES_H
#define _LINUX_TYPES_H

typedef /* unsigned */ int size_t; // XXX must watch out for architecture-related properties.
typedef size_t __kernel_size_t; // XXX I don't get why they both exist?

typedef int dma_addr_t;


// Note: architecture-dependent.
typedef unsigned char __u8;
typedef short __le16; // XXX yes? short?
typedef short __u16;

#endif