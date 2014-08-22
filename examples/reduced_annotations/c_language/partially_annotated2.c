#include "partially_annotated2.h"

int not_annotated_inc_h_2(int i)
{
  return ++i;
}

void not_annotated_c_2_1(){/*@ assert false; @*/}

int annotated_inc_2_1(int i)
  //@ requires i < 100;
  //@ ensures result == i + 1;
{
  return annotated_inc_2_2(i);
}

void not_annotated_c_2_2(){/*@ assert false; @*/}

int annotated_inc_2_2(int i)
  //@ requires i < 100;
  //@ ensures result == i + 1;
{
  return ++i;
}

void not_annotated_c_2_3(){/*@ assert false; @*/}
