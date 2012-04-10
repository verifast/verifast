#ifndef STDINT_H
#define STDINT_H

// Note that this relies on which assumptions VeriFast
// makes about the sizes of the data types, i.e.
// you cannot change this soundly without changing
// VeriFast.

typedef char  int8_t;
typedef short int16_t;
typedef int   int32_t;

typedef unsigned char   uint8_t;
typedef unsigned short  uint16_t;
typedef unsigned int    uint32_t;

#endif // STDINT_H
