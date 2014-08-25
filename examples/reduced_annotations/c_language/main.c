#include <stdio.h>
 
#include "partially_annotated1.h"
#include "partially_annotated2.h"

void not_annotated_main1(){/*@ assert false; @*/}

//@ predicate inc_predicate_main(int i, int j) = j == i + 1;

int main() //@ : main
  //@ requires true;
  //@ ensures  true;
{
  int i = 1;
  i = annotated_inc_main(i);
  //@ open inc_predicate_main(1,i);
  //@ assert i == 2;
  i = annotated_inc_1_1(i);
  //@ assert i == 3;
  i = annotated_inc_1_2(i);
  //@ assert i == 4;
  i = annotated_inc_2_1(i);
  //@ assert i == 5;
  i = annotated_inc_2_2(i);
  //@ assert i == 6;

  printf("final value:   %i\n", i);

#ifdef EXECUTE
  i = not_annotated_inc_main(i);
  printf("final value++: %i\n", i);
#endif

  return 0;
}

void not_annotated_main2(){/*@ assert false; @*/}

int not_annotated_inc_main(int i)
{
  return not_annotated_inc_h_1(i);
  
  while(true)
  {
  }
  
  /*@ assert false; @*/
}

int annotated_inc_main(int i)
  //@ requires i < 100;
  //@ ensures inc_predicate_main(i, result);
{
  //@ close inc_predicate_main(i, i + 1);
  return ++i;
}

void not_annotated_main3(){/*@ assert false; @*/}
