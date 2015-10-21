#ifndef _ARPA_INET_H
#define	_ARPA_INET_H	1

#include <stdint.h>

uint32_t ntohl (uint32_t __netlong);
//@ requires true;
//@ ensures true;

uint16_t ntohs (uint16_t __netshort);
//@ requires true;
//@ ensures true;

uint32_t htonl (uint32_t __hostlong);
//@ requires true;
//@ ensures true;

uint16_t htons (uint16_t __hostshort);
//@ requires true;
//@ ensures true;


#endif
