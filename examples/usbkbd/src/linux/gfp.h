#ifndef _LINUX_GFP_H
#define _LINUX_GFP_H

#include <linux/types.h>

// original: typedef unsigned __bitwise__ gfp_t;
typedef unsigned int __bitwise__ gfp_t;


// The problem with
// #define GFP_KERNEL	(__GFP_WAIT | __GFP_IO | __GFP_FS)
// is that VeriFast cannot typecheck it and cannot evaluate it
// (and because it cannot evaluate it, we cannot check in assertions
// that a value, constructed using GFP_KERNEL macro, has a certain
// value (32 on x86-32)).
#define GFP_KERNEL 32
#define GFP_ATOMIC 208


#endif