#ifndef HEADER2_H
#define HEADER2_H

#include "header1.h"

struct structure
{
  int value;
};
//@ predicate pred() = true;

//this is not allowed
//struct structure;
//@ predicate pred();

#endif