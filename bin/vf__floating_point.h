#ifndef VF__FLOATING_POINT_H
#define VF__FLOATING_POINT_H

//@ fixpoint real real_abs(real x) { return x < 0 ? -x : x; }

// =========== real_of_int ===========

/*@

fixpoint bool is_decimal_digit(char c) {
    return '0' <= c && c <= '9';
}

fixpoint int int_of_decimal_helper(int n, list<char> digits) {
    switch (digits) {
        case nil: return n;
        case cons(d, ds): return int_of_decimal_helper(n * 10 + (d - '0'), ds);
    }
}

fixpoint int int_of_decimal(list<char> digits) {
    return head(digits) == '-' ?
        -int_of_decimal_helper(0, tail(digits))
    :
        int_of_decimal_helper(0, digits);
}

fixpoint real real_of_decimal_digit(char d) {
    return
        d == '0' ? 0r :
        d == '1' ? 1r :
        d == '2' ? 2r :
        d == '3' ? 3r :
        d == '4' ? 4r :
        d == '5' ? 5r :
        d == '6' ? 6r :
        d == '7' ? 7r :
        d == '8' ? 8r :
        9r;
}

fixpoint real real_of_decimal_helper(real n, list<char> digits) {
    switch (digits) {
        case nil: return n;
        case cons(d, ds): return real_of_decimal_helper(n * 10 + real_of_decimal_digit(d), ds);
    }
}

fixpoint real real_of_decimal(list<char> digits) {
    return head(digits) == '-' ?
        -real_of_decimal_helper(0, tail(digits))
    :
        real_of_decimal_helper(0, digits);
}

fixpoint real real_of_int(int x);

lemma void real_of_int_of_decimal(list<char> digits);
    requires digits == cons(?d0, ?ds) &*& d0 == '-' ? forall(ds, is_decimal_digit) == true : forall(digits, is_decimal_digit) == true;
    ensures real_of_int(int_of_decimal(digits)) == real_of_decimal(digits);

@*/

// =========== floating point ===========

/*@

inductive fp = fp_real(real r) | fp_pos_inf | fp_neg_inf | fp_NaN;

fixpoint fp fp_of_float(float f);

fixpoint fp fp_of_double(double d);

fixpoint fp fp_of_long_double(long double ld);

fixpoint real float_max_error(real x) {
    return
        0x1p-126 <= real_abs(x) ? real_abs(x) * 0x0.0000_02 :
        0x0.0000_02p-126;
}

fixpoint real double_max_error(real x) {
    return
        0x1p-1022 <= real_abs(x) ? real_abs(x) * 0x0.0000_0000_0000_1 :
        0x0.0000_0000_0000_1p-1022;
}

@*/

// VeriFast interprets floating-point operations as calls of the functions declared below.

// A floating-point constant of type T is interpreted as a call of the T_of_real function.

float vf__float_of_real(real x);
    //@ requires x == 0 || 0x0.0000_02p-126 <= real_abs(x) &*& real_abs(x) <= 0x1.ffff_fep127;
    //@ ensures fp_of_float(result) == fp_real(?r) &*& x == 0 ? r == 0 : real_abs(x - r) < float_max_error(x);

double vf__double_of_real(real x);
    //@ requires x == 0 || 0x0.0000_0000_0000_1p-1022 <= real_abs(x) &*& real_abs(x) <= 0x1.ffff_ffff_ffff_fp1023;
    //@ ensures fp_of_double(result) == fp_real(?r) &*& x == 0 ? r == 0 : real_abs(x - r) < double_max_error(x);

long double vf__long_double_of_real(real x);
    //@ requires x == 0 || 0x0.0000_0000_0000_1p-1022 <= real_abs(x) &*& real_abs(x) <= 0x1.ffff_ffff_ffff_fp1023;
    //@ ensures fp_of_long_double(result) == fp_real(?r) &*& x == 0 ? r == 0 : real_abs(x - r) < double_max_error(x);

float vf__float_of_int128_t(__int128 x);
    //@ requires true;
    //@ ensures -(1 << 24) <= x && x <= (1 << 24) ? fp_of_float(result) == fp_real(real_of_int(x)) : true;

double vf__double_of_int128_t(__int128 x);
    //@ requires true;
    //@ ensures -(1 << 53) <= x && x <= (1 << 53) ? fp_of_double(result) == fp_real(real_of_int(x)) : true;

long double vf__long_double_of_int128_t(__int128 x);
    //@ requires true;
    //@ ensures -(1 << 53) <= x && x <= (1 << 53) ? fp_of_long_double(result) == fp_real(real_of_int(x)) : true;

float vf__float_of_long_long(long long x);
    //@ requires true;
    //@ ensures true;

double vf__double_of_long_long(long long x);
    //@ requires true;
    //@ ensures true;

long double vf__long_double_of_long_long (long long x);
    //@ requires true;
    //@ ensures true;

float vf__float_of_unsigned_long_long(unsigned long long x);
    //@ requires true;
    //@ ensures true;

double vf__double_of_unsigned_long_long(unsigned long long x);
    //@ requires true;
    //@ ensures true;

long double vf__long_double_of_unsigned_long_long(unsigned long long x);
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

float vf__float_of_short(short x);
    //@ requires true;
    //@ ensures true;

double vf__double_of_short(short x);
    //@ requires true;
    //@ ensures true;

long double vf__long_double_of_short(short x);
    //@ requires true;
    //@ ensures true;

float vf__float_of_unsigned_short(unsigned short x);
    //@ requires true;
    //@ ensures true;

double vf__double_of_unsigned_short(unsigned short x);
    //@ requires true;
    //@ ensures true;

long double vf__long_double_of_unsigned_short(unsigned short x);
    //@ requires true;
    //@ ensures true;

float vf__float_of_char(char x);
    //@ requires true;
    //@ ensures true;

double vf__double_of_char(char x);
    //@ requires true;
    //@ ensures true;

long double vf__long_double_of_char(char x);
    //@ requires true;
    //@ ensures true;

float vf__float_of_unsigned_char(unsigned char x);
    //@ requires true;
    //@ ensures true;

double vf__double_of_unsigned_char(unsigned char x);
    //@ requires true;
    //@ ensures true;

long double vf__long_double_of_unsigned_char(unsigned char x);
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
