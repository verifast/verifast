#ifndef __LINUX_SPINLOCK_TYPES_H
#define __LINUX_SPINLOCK_TYPES_H

struct spinlock_t_typedef_hiding;

//typedef struct spinlock_t_typedef_hiding spinlock_t; // Verifast crashes.
typedef int spinlock_t;

#endif
