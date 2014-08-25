#ifndef PARTIALLY_ANNOTATED2_H
#define PARTIALLY_ANNOTATED2_H

int not_annotated_inc_h_2(int i);

int not_annotated_h_2_1(int i);

int annotated_inc_2_1(int i);
  //@ requires i < 100;
  //@ ensures result == i + 1;

void not_annotated_h_2_2();

int annotated_inc_2_2(int i);
  //@ requires i < 100;
  //@ ensures result == i + 1;

void not_annotated_h_2_3();

#endif