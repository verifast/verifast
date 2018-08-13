#ifndef VF__EXACT_FLOATING_POINT_H
#define VF__EXACT_FLOATING_POINT_H

#define float_eps 1.192093e-7
#define double_eps 2.220446e-16
#define long_double_eps 1.084202e-19

#define f_eps 1.192093e-7
#define d_eps 2.220446e-16
#define ld_eps 1.084202e-19

// VeriFast interprets floating-point operations as calls of the functions declared below.

// A floating-point constant of type T is interpreted as a call of the T_of_real function.

// Here the (false) assumption is made that all floating point operations are exact. 
// So the floating point numbers behave like the real numbers.
/*@

fixpoint real real_abs(real x) {return x < 0 ? -x : x; }

lemma void product_sign_lemma(real x, real y);
    requires x>=0 && y>=0 || x<=0 && y<=0;
    ensures x*y >= 0;

lemma void strict_product_sign_lemma(real x, real y);
    requires x>=0 && y>=0 || x<=0 && y<=0;
    ensures x*y >= 0 &*& x == 0 || y == 0 ? x * y == 0 : 0 < x * y;

lemma void multiply_zero_lemma(real x, real y);
    requires x == 0 || y == 0;
    ensures x * y == 0;

fixpoint option<real> real_of_long_double(long double x);

fixpoint option<real> real_of_double(double x);

fixpoint option<real> real_of_float(float x);

fixpoint real real_of_int(int x);

fixpoint bool relative_error(real x, real approximation, real epsilon) {
    return approximation <= real_abs(epsilon * x) + x && approximation >= x - real_abs(epsilon * x);
}
@*/

double vf__double_of_real(real x);
    //@ requires true;
    //@ ensures real_of_double(result) == some(x);
    //@ terminates;

double vf__double_of_int(int x);
    //@ requires true;
    //@ ensures real_of_double(result) == some(real_of_int(x));
    //@ terminates;

long double vf__long_double_of_int(int x);
    //@ requires true;
    //@ ensures real_of_long_double(result) == some(real_of_int(x));
    //@ terminates;

double vf__double_of_float(float x);
    //@ requires real_of_float(x) == some(?rx);
    //@ ensures  real_of_double(result) == some(rx);
    //@ terminates;

float vf__float_of_double(double x);
    //@ requires real_of_double(x) == some(?rx);
    //@ ensures real_of_float(result) == some (?rr) &*& rx == rr;
    //@ terminates;

long double vf__long_double_of_double(double x);
    //@ requires real_of_double(x) == some(?rx);
    //@ ensures real_of_long_double(result) == some(?rresult) &*& rresult == rx;
    //@ terminates;


double vf__double_of_long_double(long double x);
    //@ requires real_of_long_double(x) == some(?rx); // rx<max_long_double
    //@ ensures real_of_double(result) == some(?rresult) &*& rresult == rx;
    //@ terminates;

bool vf__double_eq(double x, double y);
    //@ requires real_of_double(x) == some(?rx) &*& real_of_double(y) == some(?ry);
    //@ ensures result == (rx == ry);
    //@ terminates;

bool vf__double_lt(double x, double y);
    //@ requires real_of_double(x) == some(?rx) &*& real_of_double(y) == some(?ry);
    //@ ensures result == (rx < ry);
    //@ terminates;

bool vf__double_gt(double x, double y);
    //@ requires real_of_double(x) == some(?rx) &*& real_of_double(y) == some(?ry);
    //@ ensures result == (rx > ry);
    //@ terminates;

bool vf__double_ge(double x, double y);
    //@ requires real_of_double(x) == some(?rx) &*& real_of_double(y) == some(?ry);
    //@ ensures result == (rx == ry);
    //@ terminates;

double vf__double_add(double x, double y);
    //@ requires real_of_double(x) == some(?rx) &*& real_of_double(y) == some(?ry);
    //@ ensures real_of_double(result) == some(?rr) &*& rr == rx + ry;
    //@ terminates;

long double vf__long_double_add(long double x, long double y);
    //@ requires real_of_long_double(x) == some(?rx) &*& real_of_long_double(y) == some(?ry);
    //@ ensures real_of_long_double(result) == some(?rresult) &*& rresult == rx + ry;
    //@ terminates;

double vf__double_sub(double x, double y);
    //@ requires real_of_double(x) == some(?rx) &*& real_of_double(y) == some(?ry);
    //@ ensures real_of_double(result) == some(?rr) &*& rr == rx - ry;
    //@ terminates;

double vf__double_mul(double x, double y);
    //@ requires real_of_double(x) == some(?rx) &*& real_of_double(y) == some(?ry);
    //@ ensures real_of_double(result) == some(?rr) &*& rr == rx * ry;
    //@ terminates;

long double vf__long_double_div(long double x, long double y);
    //@ requires real_of_long_double(x) == some(?rx) &*& real_of_long_double(y) == some(?ry) &*& ry != 0;
    //@ ensures real_of_long_double(result) == some(?rresult) &*& rresult * ry == rx;
    //@ terminates;

#endif
