#include "rounding_math.h"



float vector_size(float x, float y)
    //@ requires real_of_float(x) == some(?rx) &*& real_of_float(y) == some(?ry);
    //@ ensures real_of_float(result) == some(?rr) &*& relative_error(real_vector_size(rx,ry),rr,0.0000102) == true;
{
    //@ strict_product_sign_lemma(rx,rx);
    //@ strict_product_sign_lemma(ry,ry);
    double x2 = (double)x * x;
    double y2 = (double)y * y;
    double sum = x2 + y2;
    double sqrt = my_sqrt(sum);
    //double sqrt = my_sqrt((double)x * x + (double)y * y);
    //@ assert real_of_double(x2) == some(?rx2);
    //@ assert real_of_double(y2) == some(?ry2);
    //@ assert real_of_double(sum) == some(?rsum);
    //@ assert real_of_double(sqrt) == some(?rsqrt);
    //@ sqrt_zero_lemma(0);

    //@ assert relative_error(rx * rx, rx2, double_eps) == true;
    //@ assert relative_error(ry * ry, ry2, double_eps) == true;
    //@ assert relative_error(rx2 + ry2,rsum,double_eps) == true;
    //@ assert relative_error(real_sqrt(rsum),rsqrt,0.00001) == true;

    //@ assert rx2 <= (rx * rx) * (1 + double_eps);
    //@ assert ry2 <= (ry * ry) * (1 + double_eps);
    //@ assert rsum <= (rx2 + ry2)*(1 + double_eps);
    //@ assert rsqrt <= real_sqrt(rsum)*1.00001;
    
    //@ assert rsum <= (1 + double_eps) * (1 + double_eps) * (rx * rx + ry * ry);
    //@ real_sqrt_lemma((1 + double_eps) * (1 + double_eps), (1 + double_eps));
    //@ sqrt_extraction_lemma((1 + double_eps) * (1 + double_eps),(rx * rx + ry * ry));
    //@ sqrt_congruence_lemma(rsum, (1 + double_eps) * (1 + double_eps) * (rx * rx + ry * ry));
    //@ assert real_sqrt(rsum) <= (1 + double_eps) * real_vector_size(rx, ry);
    //@ assert rsqrt <= 1.00001 * (1 + double_eps) * real_vector_size(rx, ry);
        
    //@ assert rx2 >= (rx * rx) * (1 - double_eps);
    //@ assert ry2 >= (ry * ry) * (1 - double_eps);
    //@ assert rsum >= (rx2 + ry2) * (1 - double_eps);
    //@ assert rsqrt >= real_sqrt(rsum)*0.99999;
    
    //@ assert rsum >= (1 - double_eps) * (1 - double_eps) * (rx * rx + ry * ry);
    //@ real_sqrt_lemma((1 - double_eps) * (1 - double_eps), (1 - double_eps));
    //@ sqrt_extraction_lemma((1 - double_eps) * (1 - double_eps),(rx * rx + ry * ry));
    //@ sqrt_congruence_lemma((1 - double_eps) * (1 - double_eps) * (rx * rx + ry * ry), rsum);
    //@ assert real_sqrt(rsum) >= real_vector_size(rx,ry) * (1 - double_eps);
    //@ assert rsqrt >= real_vector_size(rx,ry) * (1 - double_eps) * 0.99999;

    //@ assert rsqrt >= real_vector_size(rx,ry) - real_vector_size(rx,ry) * (1 - (1 - double_eps) * 0.99999);
    //@ assert rsqrt <= real_vector_size(rx,ry) + real_vector_size(rx,ry) * ((1 + double_eps) * 1.00001 - 1);
    //@ assert rsqrt >= real_vector_size(rx,ry) - real_vector_size(rx,ry) * 0.0000100001;
    //@ assert rsqrt <= real_vector_size(rx,ry) + real_vector_size(rx,ry) * 0.0000100001;
   
    return (float) sqrt;
}


double next(double r, double x)
    /*@ 
    requires real_of_double(x) == some(?rx) &*& 
    	0 < rx &*&
    	real_of_double(r) == some(?rr) &*&
    	rr > 0;
    @*/
    /*@ 
    ensures real_of_double(result) == some(?rresult) &*& 
    	rresult > 0 &*& 
    	relative_error((rr + real_div(rx,rr)) / 2,rresult,(1 + ld_eps) * (1 + ld_eps) * (1 + ld_eps) * (1 + d_eps) - 1) == true;
    @*/
    //@ terminates;
{
    //@ real_of_int_lemma_UNSAFE(2,2);
    double oldResult = r;
    long double div = (long double) x / r;
    long double sum = oldResult + div;
    long double longResult = sum / 2;
    double result = (double) longResult;
    return result;
    //@ assert real_of_double(oldResult) == some(?orr1);
    //@ assert real_of_long_double(div) == some(?ordiv1);
    //@ assert real_of_double(result) == some(?nrr1);
    //@ assert real_of_long_double(sum) == some(?rsum);
    //@ assert real_of_long_double(longResult) == some(?rlr);
    //@ real nrre = (orr1 + real_div(rx,orr1)) / 2;
    //@ real sqrx = real_sqrt(rx);
    //@ real_sqrt_lemma2(rx,sqrx);
    //@ sqrt_pos_lemma(rx);
    //@ real_div_lemma2(rx,sqrx,sqrx);
    //@ sqrt_pos_lemma(rx);
    //@ error_lemma(orr1, ordiv1, rx, nrr1, rsum, rlr);
    //@ real eps = (1 + ld_eps) * (1 + ld_eps) * (1 + ld_eps) * (1 + d_eps) - 1;
    //@ assert relative_error((orr1 + real_div(rx,orr1)) / 2,nrr1,eps) == true;
    //@ real_sqrt_lemma(orr1 * orr1,orr1);   	    

    
    //@ assert rx >= 0;
    //@ assert orr1 > 0;
    //@ real_div_pos_lemma(rx,orr1);
    //@ assert real_div(rx,orr1) >= 0;
    //@ assert ordiv1 >= 0;
    //@ assert ordiv1 + orr1 > 0;
    //@ assert rsum >= ordiv1 + orr1 - (ordiv1 + orr1) * d_eps;
    //@ assert ordiv1 + orr1 > (ordiv1 + orr1) * d_eps;
    //@ assert ordiv1 + orr1 - (ordiv1 + orr1) * d_eps > 0;
    /*@ if (rsum == ordiv1 + orr1 - (ordiv1 + orr1) * d_eps){	    
    } else {}
    @*/ 
    //@ assert rsum > 0;
    /*@ if (rlr == rsum - rsum * d_eps){
    } else {}
    @*/ 
    //@ assert rlr > 0;
    /*@ if (nrr1 == rlr - rlr * d_eps){
    } else {}
    @*/ 
    //@ assert nrr1 > 0;
}

bool test(double r, double x)
    /*@ 
    requires real_of_double(r) == some(?rr) &*& 
    	real_of_double(x) == some(?rx) &*&
    	rr > 0 &*&
    	rx > 0;
    @*/
    //@ ensures result == true ? relative_error(real_sqrt(rx), rr, 0.00001) == true : rr > real_sqrt(rx) * 1.000001 || rr < real_sqrt(rx) * 0.999999;
    //@ terminates;
{
    double a = r * r;
    double ct1 = 1.00001;
    double ct2 = 0.99999;
    double u = ct1 * x;
    double l = ct2 * x;
    //@ assert real_of_double(a) == some(?ra);
    //@ assert real_of_double(u) == some(?ru);
    //@ assert real_of_double(l) == some(?rl);
    //@ assert real_of_double(ct1) == some(?rct1);
    //@ assert real_of_double(ct2) == some(?rct2);
    if (a <= u && a >= l) {
        return true;

    	//@ stop_condition_lemma(ra,ru,rl,rct1,rct2,rr,rx);
    } else {
    	//@ not_stop_condition_lemma(ra,ru,rl,rct1,rct2,rr,rx);
        return false;
    } 
}


double my_sqrt(double x)
    /*@ 
    requires real_of_double(x) == some(?rx) &*& 
    	0 <= rx;
    @*/ 
    /*@
    ensures real_of_double(result) == some(?rr) &*& rx == 0 ? rr == 0 : 0 < rr &*& 
    	relative_error(real_sqrt(rx),rr,0.00001) == true; @*/
    //@ terminates;
{
    if (x == 0.0) return 0.0;
    //@ real_of_int_lemma_UNSAFE(1,1);
    double result = 1;  
    //@ assert real_of_double(result) == some(?nrr0);
    if (test(result,x)) {
        return result;
    }
    //@ assert nrr0 > real_sqrt(rx) * 1.000001 || nrr0 < real_sqrt(rx) * 0.999999;
    double oldResult = result;
    result = next(oldResult,x);
    //@ assert real_of_double(oldResult) == some(?orr1);
    //@ assert real_of_double(result) == some(?nrr1);
    //@ real eps = (1 + ld_eps) * (1 + ld_eps) * (1 + ld_eps) * (1 + d_eps) - 1;
    //@ real_sqrt_lemma(orr1 * orr1,orr1);   	    
    //@ real sqrx = real_sqrt(rx);
    //@ real_sqrt_lemma2(rx,sqrx);
    //@ sqrt_pos_lemma(rx);
    //@ real_div_lemma2(rx,sqrx,sqrx);
    /*@ if (orr1 * orr1 >= rx) {
    	    sqrt_congruence_lemma(rx, orr1 * orr1);
    	    division_lemma(rx,sqrx,orr1);
    	    real_div_lemma(rx,orr1,real_div(rx,orr1));
     	    overestimation_lemma1(orr1,sqrx,rx, real_div(rx,orr1), eps);
    	    assert nrr1 >= sqrx;
    	} else {
    	    sqrt_congruence_lemma(orr1 * orr1, rx);
    	    assert orr1 <= 0.999999 * sqrx;
	    real_div_lemma(rx,orr1,real_div(rx,orr1));
    	    overestimation_lemma2(orr1,sqrx,rx,real_div(rx,orr1),eps);
    	}
    @*/
    if (test(result,x)) {
        return result;
    } 
    oldResult = result;
    result = next(oldResult,x);
    //@ assert real_of_double(oldResult) == some(?orr2);
    //@ assert real_of_double(result) == some(?nrr2);
    //@ real_div_lemma(rx, orr2, real_div(rx,orr2));
    //@ overestimation_lemma1(orr2,sqrx,rx, real_div(rx,orr2), eps);
    //@ assert nrr2 >= sqrx;
    for (;;)
        /*@ invariant 
        real_of_double(result) == some(?rr) &*& 
        real_of_double(oldResult) == some(?orr) &*& 
        rr >= real_sqrt(rx) &*&
        rr - real_sqrt(rx) <= real_abs(real_sqrt(rx) - orr) &*&
        relative_error((orr + real_div(rx,orr))/2,rr, eps) == true;
        @*/
        //@ decreases real_ceiling(real_div(rr,sqrx)*1e14);
    {
    	if (test(result,x)) {
            break;
    	}
 	oldResult = result;
    	result = next(oldResult,x);
    	//@ assert real_of_double(oldResult) == some(?orr3);
    	//@ assert real_of_double(result) == some(?nrr3);
    	//@ real_div_lemma(rx, orr3, real_div(rx,orr3));
    	//@ overestimation_lemma1(orr3, sqrx, rx, real_div(rx,orr3), 1e-13);
        //@ decreases_lemma(orr3,nrr3,sqrx);
    }
    return result;
}


/*@
lemma void overestimation_lemma1(real orr, real sqrx, real rx, real ordiv, real eps)
    requires orr >= 1.000001 * sqrx &*&
    	rx == orr * ordiv &*&
    	sqrx * sqrx == rx &*&
    	eps > 0 &*&
    	eps < 4.9e-13 &*&
    	sqrx > 0;
    ensures (1 + eps) * (orr + ordiv) / 2 <= orr &*&
    	(1 - eps) * (orr + ordiv) / 2 >=  sqrx;
    {
    real_div_lemma2(rx,orr,ordiv);
    real nrre = (orr + ordiv)/2;
    real b = orr - sqrx;

    assert ordiv == real_div(rx,sqrx + b);
    real_div_sub_lemma(sqrx, b * sqrx, b + sqrx);
    assert ordiv == sqrx - real_div(b * sqrx, b + sqrx);
    real_div_sub_lemma(b, b * sqrx, b + sqrx);
    product_sign_lemma(b,b);
    real_div_pos_lemma(b * b, sqrx + b);

    assert b - real_div(b * sqrx, b + sqrx) >= 0;
    assert (nrre) >= sqrx;
    product_sign_lemma(sqrx,b);
    assert nrre == sqrx + real_div(b * b, sqrx + b) / 2;


    assert sqrx <= 1000000 * b;
    division_lemma(b,sqrx + b, 1000001 * b);
    assert real_div(b,sqrx + b ) >= real_div(b,1000001 * b);
    real_div_elimination_lemma(b, 1, 1000001);
    real_div_lemma(1,1000001,real_div(1,1000001));
    assert real_div(1,1000001) == 1 / 1000001;
    assert real_div(b,1000001 * b) == 1 / 1000001;
    assert real_div(b,sqrx + b) >= 1 / 1000001;
    
    real_div_lemma(b,sqrx,real_div(b,sqrx));
    assert b >= 0.000001 * sqrx;
    assert b / 2 >= 0.0000005 * sqrx;
    leq_preservation_lemma(0.0000005 * sqrx, b / 2, real_div(b,sqrx + b));
    assert b / 2 * real_div(b,sqrx + b) >= 0.0000005 * sqrx * real_div(b,sqrx + b);
    leq_preservation_lemma(1 / 1000001, real_div(b,sqrx + b), 0.0000005* sqrx);
    assert 0.0000005 * sqrx * real_div(b,sqrx + b)>= 0.0000005 * sqrx * 1 / 1000001;
    assert 0.0000005 * sqrx * real_div(b,sqrx + b) >=  0.0000005 * sqrx * 1 / 1000001;
    assert b / 2 * real_div(b,sqrx + b) >= 0.0000005 * sqrx * 1 / 1000001;
    real_div_extraction_lemma(b, b, sqrx + b);
    assert b / 2 * real_div(b,sqrx + b) == real_div(b * b, sqrx + b) / 2;
    assert real_div(b * b, sqrx + b) / 2 >= 0.0000005 * sqrx * 1 / 1000001;
    assert sqrx + real_div(b * b, sqrx + b) / 2 >= (0.0000005 * 1 / 1000001 + 1) * sqrx;
    assert (orr + ordiv) / 2 >= (0.0000005 * 1 / 1000001 + 1) * sqrx;
    assert sqrx <= 1000001 / 1000001.0000005 * (orr + ordiv) / 2 ;
    assert (orr + ordiv) / 2 == sqrx + real_div(b*b,sqrx + b) / 2;
    
    assert (1 - eps) >= 1000001 / 1000001.0000005;
    leq_preservation_lemma(1000001 / 1000001.0000005,(1 - eps),(orr + ordiv) / 2);
    assert 1000001 / 1000001.0000005 * (orr + ordiv) / 2 <= (1 - eps) * (orr + ordiv) / 2 ;
    assert (1 - eps) * (orr + ordiv) / 2 >=  sqrx;
    
    

    division_lemma(sqrx,1.000001 * sqrx, sqrx + b);
    assert real_div(sqrx, sqrx + b) <= real_div(1 * sqrx , 1.000001 * sqrx);
    real_div_elimination_lemma(sqrx,1,1.000001);
    real_div_lemma(1,1.000001,real_div(1, 1.000001));
    assert real_div(sqrx, sqrx + b) <= 1 / 1.000001;
    
    assert (0.5 * 1 / 1.000001 * 1 / 1.000001 + 0.5) * (1 + eps) <= 1;
    leq_preservation_lemma(real_div(sqrx, sqrx + b),1 / 1.000001, 1 / 1.000001);
    real_div_pos_lemma(sqrx, sqrx + b);
    real_sqrt_lemma(real_div(sqrx, sqrx + b) * real_div(sqrx, sqrx + b),real_div(sqrx, sqrx + b));
    real_sqrt_lemma(1 / 1.000001 * 1 / 1.000001 ,1 / 1.000001 );
    sqrt_congruence_lemma2(real_div(sqrx, sqrx + b) * real_div(sqrx, sqrx + b),1 / 1.000001 * 1 / 1.000001);
    assert 0.5 * real_div(sqrx, sqrx + b) * real_div(sqrx, sqrx + b) + 0.5 <= (0.5 * 1 / 1.000001 * 1 / 1.000001 + 0.5);
    leq_preservation_lemma(0.5 * real_div(sqrx, sqrx + b) * real_div(sqrx, sqrx + b) + 0.5,0.5 * 1 / 1.000001 * 1 / 1.000001 + 0.5, 1 + eps);
    assert (0.5 * real_div(sqrx, sqrx + b) * real_div(sqrx, sqrx + b) + 0.5) * (1 + eps) <= 1;
    real_div_product_lemma(sqrx,sqrx + b,sqrx, sqrx + b);
    assert real_div(sqrx, sqrx + b) * real_div(sqrx, sqrx + b) == real_div(sqrx * sqrx, (sqrx + b) * (sqrx + b));        
    strict_product_sign_lemma(sqrx + b, sqrx + b);
    real_div_extraction_lemma(0.5, sqrx * sqrx, (sqrx + b) * (sqrx + b));
    assert (0.5 * real_div(sqrx * sqrx, (sqrx + b) * (sqrx + b)) + 0.5)== (real_div(0.5 * sqrx * sqrx, (sqrx + b) * (sqrx + b)) + 0.5);
    real_div_add_lemma(0.5, 0.5 * sqrx * sqrx, (sqrx + b) * (sqrx + b));
    assert (0.5 * real_div(sqrx * sqrx, (sqrx + b) * (sqrx + b)) + 0.5) == real_div(0.5 * ((sqrx * sqrx) + (sqrx + b) * (sqrx + b)),(sqrx + b) * (sqrx + b));
    eq_preservation_lemma((0.5 * real_div(sqrx * sqrx, (sqrx + b) * (sqrx + b)) + 0.5),real_div(0.5 * ((sqrx * sqrx) + (sqrx + b) * (sqrx + b)),(sqrx + b) * (sqrx + b)),(1 + eps));
    assert real_div(0.5 * ((sqrx * sqrx) + (sqrx + b) * (sqrx + b)),(sqrx + b) * (sqrx + b)) * (1 + eps) <= 1;
    leq_preservation_lemma((1 + eps) * real_div(0.5 * ((sqrx * sqrx) + (sqrx + b) * (sqrx + b)),(sqrx + b) * (sqrx + b)), 1, sqrx + b); 
    assert (1 + eps) * real_div(0.5 * ((sqrx * sqrx) + (sqrx + b) * (sqrx + b)),(sqrx + b) * (sqrx + b)) * (sqrx + b) <= sqrx + b;

    real_div_extraction_lemma(sqrx + b, 0.5 * ((sqrx * sqrx) + (sqrx + b) * (sqrx + b)),(sqrx + b) * (sqrx + b));
    real_div_elimination_lemma(sqrx + b, 0.5 * ((sqrx * sqrx) + (sqrx + b) * (sqrx + b)),(sqrx + b));
    eq_preservation_lemma(real_div(0.5 * ((sqrx * sqrx) + (sqrx + b) * (sqrx + b)),(sqrx + b) * (sqrx + b)) * (sqrx + b), real_div(0.5 * ((sqrx * sqrx) + (sqrx + b) * (sqrx + b)),sqrx + b), (1 + eps));
    assert (1 + eps) * (real_div(0.5 * ((sqrx * sqrx) + (sqrx + b) * (sqrx + b)),(sqrx + b) * (sqrx + b)) * (sqrx + b)) == (1 + eps) * real_div(0.5 * ((sqrx * sqrx) + (sqrx + b) * (sqrx + b)), sqrx + b);
    associativity_lemma((1 + eps),real_div(0.5 * ((sqrx * sqrx) + (sqrx + b) * (sqrx + b)),(sqrx + b) * (sqrx + b)),(sqrx + b));
    assert (1 + eps) * (real_div(0.5 * ((sqrx * sqrx) + (sqrx + b) * (sqrx + b)),(sqrx + b) * (sqrx + b)) * (sqrx + b)) == (1 + eps) * real_div(0.5 * ((sqrx * sqrx) + (sqrx + b) * (sqrx + b)),(sqrx + b) * (sqrx + b)) * (sqrx + b);
    assert (1 + eps) * real_div(0.5 * ((sqrx * sqrx) + (sqrx + b) * (sqrx + b)), sqrx + b) <= sqrx + b;
    assert (sqrx + b) * (sqrx + b) == sqrx * sqrx + 2 * sqrx * b + b*b;
    assert (1 + eps) * real_div(0.5 * (sqrx * sqrx + sqrx * sqrx + 2 * sqrx * b + b*b), sqrx + b) <= sqrx + b;
    assert (1 + eps) * real_div(sqrx * (sqrx + b) + 0.5 *  b*b, sqrx + b) <= sqrx + b;
    real_div_sum_lemma(sqrx * (sqrx + b),0.5 *  b*b, sqrx + b);
    eq_preservation_lemma(real_div(sqrx * (sqrx + b) + 0.5 *  b*b, sqrx + b), real_div(sqrx * (sqrx + b),sqrx + b) + real_div(0.5 *  b*b, sqrx + b), 1 + eps);
    assert (1 + eps) * real_div(sqrx * (sqrx + b) + 0.5 *  b*b, sqrx + b) == (1 + eps) * ((real_div(sqrx * (sqrx + b),sqrx + b) + real_div(0.5 *  b*b, sqrx + b)));
    assert (1 + eps) * (real_div(sqrx * (sqrx + b),sqrx + b) + real_div(0.5 *  b*b, sqrx + b)) <= sqrx + b;
    real_div_extraction_lemma(0.5, b*b, sqrx + b);
    real_div_elimination_lemma(sqrx + b, sqrx, 1);
    real_div_lemma(sqrx, 1, real_div(sqrx,1));
    eq_preservation_lemma(sqrx + real_div(b * b, sqrx + b) / 2,sqrx + real_div(0.5 *  b*b, sqrx + b), 1 + eps);
    assert (1 + eps) * (sqrx + real_div(b * b, sqrx + b) / 2 )== (1 + eps) *( sqrx + real_div(0.5 *  b*b, sqrx + b));
    assert (1 + eps) * (sqrx + real_div(b * b, sqrx + b) / 2) <= sqrx + b;
    assert (sqrx + real_div(b * b, sqrx + b) / 2) * (1 + eps) <= sqrx + b;
    eq_preservation_lemma(nrre, sqrx + real_div(b * b, sqrx + b) / 2, 1 + eps);
    assert nrre * (1 + eps) <= sqrx + b;
    }

lemma void overestimation_lemma2(real orr, real sqrx, real rx, real ordiv, real eps);
    requires orr <= 0.999999 * sqrx &*&
    	rx == orr * ordiv &*&
    	sqrx * sqrx == rx &*&
    	eps > 0 &*&
    	eps < 5e-13 &*&
    	sqrx > 0;
    ensures (1 - eps) * (orr + ordiv) / 2 >=  sqrx;

    
lemma void decreases_lemma(real rr, real nrr, real sqrx)
    requires rr - nrr >= 1e-14*nrr &*&
    	sqrx > 0 &*&
    	nrr >= sqrx;
    ensures real_ceiling(real_div(rr,sqrx)*1e14) > real_ceiling(real_div(nrr,sqrx)*1e14) &*&
    	real_ceiling(real_div(nrr,sqrx)*1e14) >= 0;
    {
    real c = rr - nrr;
    assert c >= 1e-14*nrr;
    real_div_sum_lemma(nrr,c,sqrx);
    assert real_div(rr,sqrx) == real_div(nrr, sqrx) + real_div(c,sqrx);
        
    real_div_subs_lemma(1e-14*nrr,c,sqrx);
    assert real_div(c,sqrx) >= real_div(1e-14*nrr,sqrx);
    real_div_extraction_lemma(1e-14,nrr,sqrx);
    assert real_div(c,sqrx) >= 1e-14*real_div(nrr,sqrx);
    real_div_geq1(nrr,sqrx);
    assert real_div(nrr,sqrx) >= 1;
    assert real_div(c,sqrx) >= 1e-14;
       
    real_ceiling_gt_lemma(real_div(rr,sqrx)*1e14,real_div(nrr,sqrx)*1e14);
    assert real_ceiling(real_div(rr,sqrx)*1e14) > real_ceiling(real_div(nrr,sqrx)*1e14);
        
    real_ceiling_pos_lemma(real_div(nrr,sqrx)*1e14);
    assert real_ceiling(real_div(nrr,sqrx)*1e14) >= 0;
    }

lemma void error_lemma(real orr, real ordiv, real rx, real nrr, real rsum, real rlr)
    requires rx > 0 &*&
    	orr > 0 &*&
    	relative_error(real_div(rx,orr), ordiv, long_double_eps) == true &*&
    	relative_error(orr + ordiv, rsum, long_double_eps) == true &*&
    	relative_error(real_div(rsum,2), rlr, long_double_eps) == true &*&
    	relative_error(rlr,nrr, double_eps) == true;
    ensures relative_error((orr + real_div(rx,orr)) / 2,nrr,(1 + ld_eps) * (1 + ld_eps) * (1 + ld_eps) * (1 + d_eps) - 1) == true;
    {
    real_div_lemma2(orr + ordiv,2, (orr + ordiv)/2);
    real_div_lemma2(rsum,2,rsum/2);
    real_div_pos_lemma(rx,orr);
    real_div_lemma2((orr + ordiv)*(1 + ld_eps),2,(orr + ordiv)*(1 + ld_eps)/2);  
    real_div_lemma2(orr + real_div(rx,orr)*(1 + ld_eps),2,(orr + real_div(rx,orr)*(1 + ld_eps))/2);
    real_div_lemma2(orr*(1 + ld_eps) + real_div(rx,orr)*(1 + ld_eps),2,(orr*(1 + ld_eps) + real_div(rx,orr)*(1 + ld_eps))/2);    
    real_div_extraction_lemma((1 + long_double_eps), orr + real_div(rx,orr),2);
    assert nrr <= ((orr + real_div(rx,orr)) / 2) * (1 + long_double_eps) * (1 + long_double_eps) * (1 + long_double_eps) * (1 + double_eps);
    
    assert nrr >= ((orr + real_div(rx,orr)) / 2) - real_abs(((orr + real_div(rx,orr)) / 2) * ((1 + ld_eps) * (1 + ld_eps) * (1 + ld_eps) * (1 + d_eps) - 1));
    assert relative_error((orr + real_div(rx,orr)) / 2 , nrr, ((1 + ld_eps) * (1 + ld_eps) * (1 + ld_eps) * (1 + d_eps) - 1)) == true;
    }
    
lemma void stop_condition_lemma(real ra, real ru, real rl, real rct1, real rct2, real nrr, real rx)
    requires ra <= ru &*&
    	ra >= rl &*&
    	rx > 0 &*&
    	nrr > 0 &*&
    	relative_error(nrr * nrr, ra, double_eps) == true &*&
    	relative_error(0.99999, rct2, d_eps) == true &*&
    	relative_error(1.00001, rct1, d_eps) == true &*&
    	relative_error(rx * rct2, rl , d_eps) == true &*&
    	relative_error(rx * rct1, ru , d_eps) == true;
    ensures relative_error(real_sqrt(rx), nrr, 0.00001) == true;
{
        
    product_sign_lemma(rx,rct2);
    assert rl >= rx * rct2 * md_eps;
    assert rct2 >= 0.99999 * md_eps;
    assert rx * (1 - d_eps) > 0;
    leq_preservation_lemma(0.99999 * md_eps, rct2, rx * md_eps);
    assert rct2 * rx * md_eps >= 0.99999 * md_eps * rx * md_eps;
    leq_transitivity_lemma(rx * 0.99999 * md_eps * md_eps,rx * rct2 * md_eps,rl);
    assert rl >= rx * 0.99999 * md_eps * md_eps;
    product_sign_lemma(rx,rct1);
    assert ru <= rx * rct1 * pd_eps;
    assert rct1 <= 1.00001 * pd_eps;
    leq_preservation_lemma(rct1, 1.00001 * pd_eps,rx * pd_eps);
    assert ru <= rx * 1.00001 * pd_eps * pd_eps;
    
    assert ra <= nrr * nrr * pd_eps;
    assert ra >= nrr * nrr * md_eps;
    assert ra / pd_eps <= nrr * nrr;
    assert ra / md_eps >= nrr * nrr;
    sqrt_congruence_lemma(ra / pd_eps, nrr * nrr);
    sqrt_congruence_lemma(nrr * nrr, ra / md_eps);
    real_sqrt_lemma(nrr*nrr,nrr);
    assert nrr >= real_sqrt(ra / pd_eps);
    assert nrr <= real_sqrt(ra / md_eps);
    sqrt_congruence_lemma(rl / pd_eps, ra / pd_eps);
    sqrt_congruence_lemma(ra / md_eps, ru / md_eps);
    assert nrr >= real_sqrt(rl / pd_eps);
    assert nrr <= real_sqrt(ru / md_eps);
    sqrt_congruence_lemma(rx * 0.99999 * md_eps * md_eps / pd_eps, rl / pd_eps);
    assert nrr >= real_sqrt(rx * 0.99999 * md_eps * md_eps / pd_eps);
    sqrt_congruence_lemma(ru / md_eps,rx * 1.00001 * (1 + d_eps) * (1 + d_eps) / md_eps);
    assert nrr <= real_sqrt(rx * 1.00001 * pd_eps * pd_eps / md_eps);
    sqrt_extraction_lemma(rx,1.00001 * pd_eps * pd_eps / md_eps);
    sqrt_extraction_lemma(rx,0.99999 * (1 - d_eps) * (1 - d_eps) / pd_eps);	
    assert nrr <= real_sqrt(rx) * real_sqrt(1.00001 * pd_eps * pd_eps / md_eps);
    assert nrr >= real_sqrt(rx) * real_sqrt(0.99999 * md_eps * md_eps / pd_eps);	
    sqrt_congruence_lemma(0.99999*0.99999, 0.99999 * md_eps * md_eps / pd_eps);
    real_sqrt_lemma(0.99999*0.99999,0.99999);
    sqrt_congruence_lemma(1.00001 * pd_eps * pd_eps / md_eps, 1.00001*1.00001);
    real_sqrt_lemma(1.00001*1.00001,1.00001);
    assert real_sqrt(1.00001 * pd_eps * pd_eps / md_eps) <= 1.00001;
    assert real_sqrt(0.99999 * (1 - d_eps) * (1 - d_eps) / pd_eps) >= 0.99999;
    sqrt_pos_lemma(rx);
    leq_preservation_lemma(real_sqrt(1.00001 * pd_eps * pd_eps / md_eps),1.00001,real_sqrt(rx));
    assert real_sqrt(1.00001 * pd_eps * pd_eps / md_eps) * real_sqrt(rx) <= 1.00001 * real_sqrt(rx);

    leq_preservation_lemma(0.99999,real_sqrt(0.99999 * md_eps * md_eps / pd_eps),real_sqrt(rx));
    assert nrr <= real_sqrt(rx) * 1.00001;
    assert nrr >= real_sqrt(rx) * 0.99999;
    assert relative_error(real_sqrt(rx), nrr, 0.00001) == true;
}

lemma void not_stop_condition_lemma(real ra, real ru, real rl, real rct1, real rct2, real nrr, real rx)
    requires ra > ru || ra < rl &*&
    	nrr > 0 &*&
    	rx > 0 &*&
    	relative_error(nrr * nrr, ra, double_eps) == true &*&
    	relative_error(0.99999, rct2, d_eps) == true &*&
    	relative_error(1.00001, rct1, d_eps) == true &*&
    	relative_error(rx * rct2, rl , d_eps) == true &*&
    	relative_error(rx * rct1, ru , d_eps) == true;
    ensures nrr > real_sqrt(rx) * 1.000001 || nrr < real_sqrt(rx) * 0.999999;
{
    sqrt_pos_lemma(rx);
    product_sign_lemma(rx,rct2);
    assert rl <= rx * rct2 * (1 + d_eps);
    assert rct2 <= 0.99999*(1 + d_eps);
    leq_preservation_lemma(rct2, 0.99999 * (1 + d_eps), rx * (1 + d_eps));
    assert rct2 * rx * (1 + d_eps) <= 0.99999*(1 + d_eps) * rx * (1 + d_eps);
    leq_transitivity_lemma(rl, rx * rct2 * (1 + d_eps), rx * 0.99999 * (1 + d_eps) * (1 + d_eps));
    assert rl <= rx * 0.99999 * (1 + d_eps) * (1 + d_eps);
    product_sign_lemma(rx,rct1);
    assert ru >= rx * rct1 * (1 - d_eps);
    assert rct1 >= 1.00001 * (1 - d_eps);
    leq_preservation_lemma(1.00001 * (1 - d_eps), rct1, rx * (1 - d_eps));
    assert ru >= 1.00001 * rx * (1 - d_eps) * (1 - d_eps);
    
    strict_product_sign_lemma(nrr,nrr);
    assert ra <= nrr * nrr * (1 + double_eps);
    assert ra >= nrr * nrr * (1 - double_eps);
    assert ra / 1.0000000000000002220446 <= nrr * nrr; // 1 + double_eps
    assert ra / 0.9999999999999997779554 >= nrr * nrr; // 1 - double_eps;
    sqrt_congruence_lemma(ra / 1.0000000000000002220446, nrr * nrr);
    sqrt_congruence_lemma(nrr * nrr, ra / 0.9999999999999997779554);
    real_sqrt_lemma(nrr*nrr,nrr);
    assert nrr >= real_sqrt(ra / 1.0000000000000002220446);
    assert nrr <= real_sqrt(ra / 0.9999999999999997779554);
    if (ra > ru) {
    	sqrt_congruence_lemma(ru / 1.0000000000000002220446, ra / 1.0000000000000002220446);
    	assert nrr >= real_sqrt(ru / 1.0000000000000002220446);
    	sqrt_congruence_lemma(1.00001 * rx * (1 - d_eps) * (1 - d_eps) / 1.0000000000000002220446, ru / 1.0000000000000002220446);
    	assert nrr >= real_sqrt(rx * 1.00001 * (1 - d_eps) * (1 - d_eps) / 1.0000000000000002220446);
    	sqrt_extraction_lemma(rx, 1.00001 * (1 - d_eps) * (1 - d_eps) / 1.0000000000000002220446);
    	assert nrr >= real_sqrt(rx) * real_sqrt(1.00001 * (1 - d_eps) * (1 - d_eps) / 1.0000000000000002220446);
    	sqrt_congruence_lemma(1.000009,1.00001 * (1 - d_eps) * (1 - d_eps) / 1.0000000000000002220446);
    	leq_preservation_lemma(real_sqrt(1.000009),real_sqrt(1.00001 * (1 - d_eps) * (1 - d_eps) / 1.0000000000000002220446), real_sqrt(rx));
    	assert nrr >= real_sqrt(rx) * real_sqrt(1.000009);
    	sqrt_congruence_lemma(1.000004*1.000004,1.000009);
    	real_sqrt_lemma(1.000004*1.000004,1.000004);
    	leq_preservation_lemma(1.000004,real_sqrt(1.000009),real_sqrt(rx));
    	assert nrr >= real_sqrt(rx) * 1.000004;   	
    } else {
        assert ra < rl;
        sqrt_congruence_lemma(ra / 0.9999999999999997779554, rl / 0.9999999999999997779554);
        assert nrr <= real_sqrt(rl / 0.9999999999999997779554);
        sqrt_congruence_lemma(rl / 0.9999999999999997779554, rx * 0.99999 * (1 + d_eps) * (1 + d_eps) / 0.9999999999999997779554);
        sqrt_extraction_lemma(rx, 0.99999 * (1 + d_eps) * (1 + d_eps) / 0.9999999999999997779554);
        sqrt_congruence_lemma(0.99999 * (1 + d_eps) * (1 + d_eps) / 0.9999999999999997779554, 0.999991);
        leq_preservation_lemma(real_sqrt(0.99999 * (1 + d_eps) * (1 + d_eps) / 0.9999999999999997779554), real_sqrt(0.999991), real_sqrt(rx));
        assert nrr <= real_sqrt(rx) * real_sqrt(0.999991);
        sqrt_congruence_lemma(0.999991, 0.999996*0.999996);
        real_sqrt_lemma(0.999996*0.999996,0.999996);
        leq_preservation_lemma(real_sqrt(0.999991),0.999996,real_sqrt(rx));
        assert nrr <= real_sqrt(rx) * 0.999996;
    }
    
}


@*/

