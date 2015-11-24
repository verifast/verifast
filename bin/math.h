#ifndef MATH_H
#define MATH_H

float vf__float_of_int(int x);
    //@ requires true;
    //@ ensures true;

double vf__double_of_int(int x);
    //@ requires true;
    //@ ensures true;

long double vf__long_double_of_int(int x);
    //@ requires true;
    //@ ensures true;

bool vf__float_eq(float x, float y);
    //@ requires true;
    //@ ensures true;

bool vf__double_eq(double x, double y);
    //@ requires true;
    //@ ensures true;

bool vf__long_double_eq(long double x, long double y);
    //@ requires true;
    //@ ensures true;

bool vf__float_neq(float x, float y);
    //@ requires true;
    //@ ensures true;

bool vf__double_neq(double x, double y);
    //@ requires true;
    //@ ensures true;

bool vf__long_double_neq(long double x, long double y);
    //@ requires true;
    //@ ensures true;

double fabs(double x);
    //@ requires true;
    //@ ensures true;

#endif