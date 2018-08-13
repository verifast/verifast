#include "exact_math.h"

float vector_size(float x, float y)
    /*@ requires real_of_float(x) == some(?rx) &*&
    	real_of_float(y) == some(?ry); @*/
    /*@ ensures real_of_float(result) == some(?rr) &*&
    	rx == 0 && ry == 0 ? rr == 0 : 0 < rr &*& 
        relative_error(real_vector_size(rx,ry),rr,0.00001) == true; @*/
{
    //@ strict_product_sign_lemma(rx,rx);
    //@ strict_product_sign_lemma(ry,ry);
    double sqrt = my_sqrt((double)x * x + (double)y * y);
    return (float) sqrt;
}

double my_sqrt(double x)
    //@ requires real_of_double(x) == some(?rx) &*& 0 <= rx;
    /*@ ensures real_of_double(result) == some(?rr) &*& 
    rx == 0 ? rr == 0 : 0 < rr &*& 
    relative_error(real_sqrt(rx),rr,0.00001) == true; @*/
    //@ terminates;
{
    if (x == 0.0) return 0.0;
    double result = 1.0;
    double oldResult = result;
    long double div = (long double) x / result;
    //@ real_of_int_lemma_UNSAFE(2,2);
    result = (oldResult + div) / 2;
    //@ assert real_of_double(oldResult) == some(?orr1);
    //@ assert real_of_long_double(div) == some(?ordiv1);
    //@ real_sqrt_lemma(orr1 * orr1,orr1);   	    
    //@ real_div_lemma2(rx,orr1,ordiv1);
    //@ real sqrx = real_sqrt(rx);
    //@ real_sqrt_lemma2(rx,sqrx);
    //@ sqrt_pos_lemma(rx);
    //@ real_div_lemma2(rx,sqrx,sqrx);
    /*@ if (orr1 * orr1 >= rx) {
    	    sqrt_congruence_lemma(rx, orr1 * orr1);
    	    division_lemma(rx,sqrx,orr1);
    	    overestimation_lemma1(orr1,ordiv1,rx,sqrx);
    	} else {
    	    strict_sqrt_congruence_lemma(orr1 * orr1, rx);
	    overestimation_lemma2(orr1,ordiv1,rx,sqrx);
    	}
    @*/
    oldResult = result;
    div = (long double) x / result;
    result = (oldResult + div) / 2;
    //@ assert real_of_double(oldResult) == some(?orr2);
    //@ assert real_of_long_double(div) == some(?ordiv2);
    
    //@ overestimation_lemma1(orr2,ordiv2,rx,sqrx);
    
    for (;;)
        /*@ invariant 
        real_of_double(result) == some(?rr) &*& 
        real_of_double(oldResult) == some(?orr) &*& 
	real_of_long_double(div) == some(?ordiv) &*&
        rr >= real_sqrt(rx) &*&
        rr - real_sqrt(rx) <= real_abs(real_sqrt(rx) - orr) &*&
        rr == (orr + ordiv)/2;
        @*/
        //@ decreases real_ceiling(real_div(rr,sqrx)*1000000);
    {
        oldResult = result;
        div = (long double)x / result;
        result = (result + div) / 2;
    	//@ assert real_of_long_double(div) == some(?rdiv);
    	//@ assert real_of_double(result) == some(?nrr);
    	//@ overestimation_lemma1(rr,rdiv,rx,sqrx);
        double rDif = oldResult - result;
        if (rDif < 0.000004*result) {
            break;
        }
        //@ decreases_lemma(rr,nrr,sqrx);
    }
    return result;
}

/*@
lemma void overestimation_lemma1(real orr2,real ordiv2,real rx,real sqrx)
    requires orr2 >= sqrx &*& 
    	rx == orr2 * ordiv2 &*&
    	sqrx * sqrx == rx &*&
    	sqrx > 0;
    ensures ordiv2 <= sqrx &*& 
    	real_div(rx,orr2) == ordiv2 &*&
    	(orr2 + ordiv2)/2 >= sqrx;
{
    real_div_lemma2(rx,orr2,ordiv2);
    real rr2 = (orr2 + ordiv2)/2;
    real b1 = orr2 - sqrx;
    assert ordiv2 == real_div(rx,sqrx + b1);
    real_div_sub_lemma(sqrx, b1 * sqrx, b1 + sqrx);
    assert ordiv2 == sqrx - real_div(b1 * sqrx, b1 + sqrx);
    real_div_sub_lemma(b1, b1 * sqrx, b1 + sqrx);
    product_sign_lemma(b1,b1);
    real_div_pos_lemma(b1 * b1, sqrx + b1);
    assert b1 - real_div(b1 * sqrx, b1 + sqrx) >= 0;
    assert (rr2) >= sqrx;
    product_sign_lemma(sqrx,b1);
    assert sqrx * b1 >= 0;
    real_div_pos_lemma(b1 * sqrx, b1 + sqrx);
    assert real_div(b1 * sqrx, b1 + sqrx) >= 0;
    assert ordiv2 <= sqrx;
}

lemma void overestimation_lemma2(real orr1, real ordiv1, real rx, real sqrx)
    requires orr1 < sqrx &*& 
    	rx == orr1 * ordiv1 &*&
    	sqrx * sqrx == rx &*&
    	orr1 > 0 &*&
    	ordiv1 == real_div(rx,orr1) &*&
    	sqrx > 0;
    ensures ordiv1 >= sqrx &*& 
    	real_div(rx,orr1) == ordiv1 &*&
    	(orr1 + ordiv1)/2 >= sqrx;
{
    real rr1 = (orr1 + ordiv1)/2;
    assert sqrx > orr1;
    real b = sqrx - orr1;
    assert ordiv1 == real_div(rx,sqrx - b); 
    real_div_add_lemma(sqrx, b * sqrx, sqrx - b);
    assert ordiv1 == sqrx + real_div(b * sqrx, sqrx - b); 
    real_div_sub_lemma2(b, b * sqrx, sqrx - b);
    product_sign_lemma(b,b);
    real_div_pos_lemma(b * b, sqrx - b);
    assert real_div(b * sqrx,sqrx - b) - b >= 0; 
    assert rr1 >= sqrx;
    assert real_abs(sqrx - orr1) == sqrx - orr1;
    assert rr1 <= ordiv1;
    assert rr1 >= orr1;
    }
    
lemma void decreases_lemma(real rr, real nrr, real sqrx)
    requires rr - nrr >= 0.000004*nrr &*&
    	sqrx > 0 &*&
    	nrr >= sqrx;
    ensures real_ceiling(real_div(rr,sqrx)*1000000) > real_ceiling(real_div(nrr,sqrx)*1000000) &*&
    	real_ceiling(real_div(nrr,sqrx)*1000000) >= 0;
{
    real c = rr - nrr;
    assert c >= 0.000004*nrr;
    real_div_sum_lemma(nrr,c,sqrx);
    assert real_div(rr,sqrx) == real_div(nrr, sqrx) + real_div(c,sqrx);
        
    real_div_subs_lemma(0.000004*nrr,c,sqrx);
    assert real_div(c,sqrx) >= real_div(0.000004*nrr,sqrx);
    real_div_extraction_lemma(0.000004,nrr,sqrx);
    assert real_div(c,sqrx) >= 0.000004*real_div(nrr,sqrx);
    real_div_geq1(nrr,sqrx);
    assert real_div(nrr,sqrx) >= 1;
    assert real_div(c,sqrx) >= 0.000004;
       
    real_ceiling_gt_lemma(real_div(rr,sqrx)*1000000,real_div(nrr,sqrx)*1000000);
    assert real_ceiling(real_div(rr,sqrx)*1000000) > real_ceiling(real_div(nrr,sqrx)*1000000);
        
    real_ceiling_pos_lemma(real_div(nrr,sqrx)*1000000);
    assert real_ceiling(real_div(nrr,sqrx)*1000000) >= 0;
    }  
 @*/   
    
