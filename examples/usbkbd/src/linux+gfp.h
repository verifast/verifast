#ifndef _LINUX_GFP_H
#define _LINUX_GFP_H

#define __bitwise__

// original: typedef unsigned __bitwise__ gfp_t;
typedef unsigned int __bitwise__ gfp_t;


// VeriFast crashes on
// #define GFP_KERNEL	(__GFP_WAIT | __GFP_IO | __GFP_FS)
// because it wants to take what is between brackets as argument list...
 
#define GFP_KERNEL 32
/*@
#define GFP_KERNEL 32
@*/
#define GFP_ATOMIC 208
/*@
#define GFP_ATOMIC 208
@*/


#endif