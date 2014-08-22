#include "partially_annotated1.h"
#include "partially_annotated2.h"

int not_annotated_inc_h_1(int i)
{
/*@ assert false; @*/ 
  return not_annotated_inc_h_2(i); 
}
void not_annotated_c_1_1(){/*@ assert false; @*/}

int annotated_inc_1_1(int i)
  //@ requires i < 100;
  //@ ensures result == i + 1;
{
  int j = 1;
  j = annotated_inc_1_2(j);
  //@ assert j == 2;
  j = annotated_inc_2_1(j);
  //@ assert j == 3;
  j = annotated_inc_2_2(j);
  //@ assert j == 4;
  return ++i;
}

void not_annotated_c_1_2(){/*@ assert false; @*/}

int annotated_inc_1_2(int i)
  //@ requires i < 100;
  //@ ensures result == i + 1;
{
  return ++i;
}

void not_annotated_c_1_3(){/*@ assert false; @*/}
