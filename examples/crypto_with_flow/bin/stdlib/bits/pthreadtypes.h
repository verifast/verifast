#ifndef PTHREADTYPES_H
#define PTHREADTYPES_H


typedef unsigned long pthread_t;

typedef volatile int pthread_spinlock_t;

// TODO: This is supposed to be a union!
struct pthread_attr
{
  char __size[36]; // 32 bit environments only!
  long __align;
};

typedef struct pthread_attr pthread_attr_t;


#endif
