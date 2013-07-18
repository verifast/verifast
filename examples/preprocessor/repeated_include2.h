#ifndef REPEATED_INCLUDE_H
#define REPEATED_INCLUDE_H

#include "repeated_include.h"

int ret_val()
//@ requires true;
//@ ensures true;
{
	return CONST;
}

#endif