#ifndef PARTIALLY_ANNOTATED1_H
#define PARTIALLY_ANNOTATED1_H

int not_annotated_inc_h_1(int i);

int not_annotated_1_1(int i);

int annotated_inc_1_1(int i);
  //@ requires i < 100;
  //@ ensures result == i + 1;

void not_annotated_h_1_2();

int annotated_inc_1_2(int i);
  //@ requires i < 100;
  //@ ensures result == i + 1;

void not_annotated_h_1_3();

#endif
