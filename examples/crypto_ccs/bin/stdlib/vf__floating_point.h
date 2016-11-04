#ifndef VF__FLOATING_POINT_H
#define VF__FLOATING_POINT_H

// VeriFast interprets floating-point operations as calls of the functions declared below.

// A floating-point constant of type T is interpreted as a call of the T_of_real function.

float vf__float_of_real(real x);
    //@ requires true;
    //@ ensures true;

double vf__double_of_real(real x);
    //@ requires true;
    //@ ensures true;

long double vf__long_double_of_real(real x);
    //@ requires true;
    //@ ensures true;

float vf__float_of_int(int x);
    //@ requires true;
    //@ ensures true;

double vf__double_of_int(int x);
    //@ requires true;
    //@ ensures true;

long double vf__long_double_of_int(int x);
    //@ requires true;
    //@ ensures true;

float vf__float_of_unsigned_int(unsigned int x);
    //@ requires true;
    //@ ensures true;

double vf__double_of_unsigned_int(unsigned int x);
    //@ requires true;
    //@ ensures true;

long double vf__long_double_of_unsigned_int(unsigned int x);
    //@ requires true;
    //@ ensures true;

double vf__double_of_float(float x);
    //@ requires true;
    //@ ensures true;

long double vf__long_double_of_float(float x);
    //@ requires true;
    //@ ensures true;

float vf__float_of_double(double x);
    //@ requires true;
    //@ ensures true;

long double vf__long_double_of_double(double x);
    //@ requires true;
    //@ ensures true;

float vf__float_of_long_double(long double x);
    //@ requires true;
    //@ ensures true;

double vf__double_of_long_double(long double x);
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

bool vf__float_lt(float x, float y);
    //@ requires true;
    //@ ensures true;

bool vf__double_lt(double x, double y);
    //@ requires true;
    //@ ensures true;

bool vf__long_double_lt(long double x, long double y);
    //@ requires true;
    //@ ensures true;

bool vf__float_le(float x, float y);
    //@ requires true;
    //@ ensures true;

bool vf__double_le(double x, double y);
    //@ requires true;
    //@ ensures true;

bool vf__long_double_le(long double x, long double y);
    //@ requires true;
    //@ ensures true;

bool vf__float_gt(float x, float y);
    //@ requires true;
    //@ ensures true;

bool vf__double_gt(double x, double y);
    //@ requires true;
    //@ ensures true;

bool vf__long_double_gt(long double x, long double y);
    //@ requires true;
    //@ ensures true;

bool vf__float_ge(float x, float y);
    //@ requires true;
    //@ ensures true;

bool vf__double_ge(double x, double y);
    //@ requires true;
    //@ ensures true;

bool vf__long_double_ge(long double x, long double y);
    //@ requires true;
    //@ ensures true;

float vf__float_add(float x, float y);
    //@ requires true;
    //@ ensures true;

double vf__double_add(double x, double y);
    //@ requires true;
    //@ ensures true;

long double vf__long_double_add(long double x, long double y);
    //@ requires true;
    //@ ensures true;

float vf__float_sub(float x, float y);
    //@ requires true;
    //@ ensures true;

double vf__double_sub(double x, double y);
    //@ requires true;
    //@ ensures true;

long double vf__long_double_sub(long double x, long double y);
    //@ requires true;
    //@ ensures true;

float vf__float_mul(float x, float y);
    //@ requires true;
    //@ ensures true;

double vf__double_mul(double x, double y);
    //@ requires true;
    //@ ensures true;

long double vf__long_double_mul(long double x, long double y);
    //@ requires true;
    //@ ensures true;

float vf__float_div(float x, float y);
    //@ requires true;
    //@ ensures true;

double vf__double_div(double x, double y);
    //@ requires true;
    //@ ensures true;

long double vf__long_double_div(long double x, long double y);
    //@ requires true;
    //@ ensures true;

#endif