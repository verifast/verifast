#ifndef ROUNDING_MATH_H
#define ROUNDING_MATH_H


#include "vf__rounding_floating_point.h"

double fabs(double x);
    //@ requires real_of_double(x) == some(?rx);
    //@ ensures real_of_double(result) == some(?rresult) &*& rresult >=0 &*& rresult == rx || rresult == -rx;
    //@ terminates;
    
double nextafter(double x, double y);


/*@ 

lemma void leq_substitution_lemma(real x, real y, real z);
    requires x <= y &*& y == z;
    ensures x <= z;
    
lemma void leq_transitivity_lemma(real a, real b, real c)
    requires a <= b &*& b <= c;
    ensures a <= c;
    {}
    
lemma void associativity_lemma(real a, real b, real c);
    requires true;
    ensures a * b * c == a * (b * c);
    
lemma void leq_preservation_lemma(real x, real y, real z);
    requires x <= y &*& z >= 0;
    ensures x * z <= y * z;
    
lemma void eq_preservation_lemma(real x, real y ,real z);
    requires x == y;
    ensures z * x == z * y;
    
lemma void geq_substitution_lemma(real x, real y , real z);
    requires x >= y &*& y == z;
    ensures x >= z;

lemma void substitution_lemma(real x, real y, real z, real w);
    requires x == y + z &*& y == w;
    ensures x == w + z;   
    
lemma void product_substitution_lemma(real a, real b, real c);
    requires b <= c &*& a >= 0;
    ensures a * b <= a * c;
    

lemma void real_div_lemma(real x, real y, real result);
    requires real_div(x,y) == result &*& y != 0;
    ensures x == y * result;
    
lemma void real_div_lemma2(real x, real y, real result);
    requires x == y * result &*& y != 0;
    ensures real_div(x,y) == result;

lemma void division_lemma(real num, real small, real big);
    requires small <= big &*& num >=0 &*& small > 0;
    ensures real_div(num,small) >= real_div(num,big);
    
lemma void real_div_sum_lemma(real a, real b, real c);
    requires c != 0;
    ensures real_div(a + b, c) == real_div(a,c) + real_div(b,c);
    
lemma void real_div_geq1(real a, real b);
    requires a >= b &*& a >= 0 &*& b > 0;
    ensures real_div(a,b) >= 1;
    
lemma void real_div_subs_lemma(real a, real b, real c);
    requires a <= b &*& c > 0;
    ensures real_div(a,c) <= real_div(b,c);
    
lemma void real_div_extraction_lemma(real b, real c, real d);
    requires d != 0;
    ensures real_div(b * c, d) == b * real_div(c,d);
    
lemma void real_div_elimination_lemma(real a, real b, real c);
    requires a != 0;
    ensures real_div(a * b, a * c) == real_div(b,c);
    
lemma void real_div_sub_lemma(real a, real x, real y);
    requires y != 0;
    ensures a - real_div(x,y) == real_div(a * y - x , y);
    
lemma void real_div_sub_lemma2(real a, real x, real y);
    requires y != 0;
    ensures real_div(x,y) - a == real_div(x - a * y, y);
    
lemma void real_div_add_lemma(real a, real x, real y);
    requires y != 0;
    ensures a + real_div(x,y) == real_div(a * y + x,y);
   
lemma void real_div_pos_lemma(real x, real y);
    requires (x >= 0 && y > 0);
    ensures real_div(x,y) >= 0;
   
lemma void real_div_product_lemma(real a, real b, real c, real d);
    requires b != 0 &*& d != 0;
    ensures real_div(a,b) * real_div(c,d) == real_div(a * c, b * d);

lemma void real_of_int_lemma_UNSAFE(int x, real rx);
    requires true;
    ensures real_of_int(x) == rx;


fixpoint real real_sqrt(real x);

lemma void real_sqrt_lemma(real x, real sqrt);
    requires sqrt * sqrt == x &*& sqrt >= 0;
    ensures real_sqrt(x) == sqrt;
    
lemma void real_sqrt_lemma2(real x, real sqrt);
    requires real_sqrt(x) == sqrt &*& x >= 0;
    ensures sqrt * sqrt == x;
    
lemma void sqrt_pos_lemma(real x);
    requires x > 0;
    ensures real_sqrt(x) > 0;
    
lemma void sqrt_congruence_lemma(real x, real y);
    requires x <= y &*& x>=0;
    ensures real_sqrt(x) <= real_sqrt(y);
    
lemma void sqrt_congruence_lemma2(real x, real y);
    requires real_sqrt(x) <= real_sqrt(y);
    ensures  x <= y;
    
lemma void strict_sqrt_congruence_lemma(real x, real y);
    requires x < y &*& x>=0 &*& y>=0;
    ensures real_sqrt(x) < real_sqrt(y);
    
lemma void sqrt_extraction_lemma(real x, real y);
    requires x >= 0 &*& y >= 0;
    ensures real_sqrt(x*y) == real_sqrt(x) * real_sqrt(y);
    
lemma void sqrt_zero_lemma(real x);
    requires x == 0;
    ensures real_sqrt(x) == 0;
    
lemma void sqrt_leq_one_lemma(real x);
    requires x <= 1 &*& x >= 0;
    ensures real_sqrt(x) <= 1;
    
lemma void sqrt_geq_one_lemma(real x);
    requires x >= 1;
    ensures real_sqrt(x) >= 1;
    
fixpoint real real_vector_size(real x, real y){
    return real_sqrt(x * x + y * y);
} 

fixpoint int real_ceiling(real x);
    
lemma void real_ceiling_gt_lemma(real a, real b);
    requires a - b >= 1;
    ensures real_ceiling(a) > real_ceiling(b);

lemma void real_ceiling_pos_lemma(real a);
    requires a >= 0;
    ensures real_ceiling(a) >= 0;
    
@*/



#endif
