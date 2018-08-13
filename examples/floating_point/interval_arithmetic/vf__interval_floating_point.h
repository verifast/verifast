#ifndef VF__INTERVAL_FLOATING_POINT_H
#define VF__INTERVAL_FLOATING_POINT_H

#define float_eps 1.192093e-7
#define double_eps 2.220446e-16
#define long_double_eps 1.084202e-19
#define f_eps 1.192093e-7
#define d_eps 2.220446e-16
#define ld_eps 1.084202e-19

#define md_eps 0.9999999999999997779554 // = 1 - d_eps
#define pd_eps 1.0000000000000002220446 // = 1 + d_eps

#define max_dbl 179769313486231570814527423731704356798070567525844996598917476803157260780028538760589558632766878171540458953514382464234321326889464182768467546703537516986049910576551282076245490090389328944075868508455133942304583236903222948165808559332123348274797826204144723168738177180919299881250404026184124858368.0
#define min_dbl -max_dbl

// VeriFast interprets floating-point operations as calls of the functions declared below.

// A floating-point constant of type T is interpreted as a call of the T_of_real function.

//The functions here work correctly with rounding error, infinity, NaN and overflow but do not account for signed zero or underflow.


/*@

lemma void real_double_lemma(double x);
    requires fp_of_double(x) == real_double(?rx);
    ensures rx <= max_dbl &*& rx >= min_dbl;

fixpoint real real_div(real x, real y);
fixpoint real real_abs(real x) {return x < 0 ? -x : x; }

lemma void product_sign_lemma(real x, real y);
    requires x>=0 && y>=0 || x<=0 && y<=0;
    ensures x*y >= 0;

lemma void product_sign_lemma2(real x, real y);
    requires x*y >= 0;
    ensures x>=0 && y>=0 || x<=0 && y<=0;

lemma void strict_product_sign_lemma(real x, real y);
    requires x>=0 && y>=0 || x<=0 && y<=0;
    ensures x*y >= 0 &*& x == 0 || y == 0 ? x * y == 0 : 0 < x * y;

lemma void multiply_zero_lemma(real x, real y);
    requires x == 0 || y == 0;
    ensures x * y == 0;
    
lemma void negative_product_lemma(real x, real y);
    requires x <= 0 &*& y >= 0;
    ensures x * y <= 0;

fixpoint option<real> real_of_long_double(long double x);
fixpoint option<real> real_of_double(double x);
fixpoint option<real> real_of_float(float x);
fixpoint real real_of_int(int x);

fixpoint fp_double fp_of_double(double x);	

inductive fp_double = real_double(real) | pos_inf | neg_inf | NaN;

fixpoint bool is_real_double(double x){
    return !(fp_of_double(x) == pos_inf || fp_of_double(x) == neg_inf || fp_of_double(x) == NaN);
}

fixpoint real next_double(real x);
fixpoint real prev_double(real x);
fixpoint real round_up_double(real x);
fixpoint real round_down_double(real x);


lemma void next_double_lemma(real x, real next);
    requires next == next_double(x);
    ensures next > x &*&
    	next <= x + real_abs(x * d_eps);
  
lemma void prev_double_lemma(real x, real prev);
    requires prev == prev_double(x);
    ensures prev < x &*&
    	prev >= x - real_abs(x * d_eps);

lemma void round_up_min_dbl_lemma(real x);
    requires x <= min_dbl;
    ensures round_up_double(x) == min_dbl;
 
lemma void round_down_max_dbl_lemma(real x);
    requires x >= max_dbl;
    ensures round_down_double(x) == max_dbl;     
    
lemma void next_double_transitivity_lemma(real a, real b);
    requires a <= b;
    ensures next_double(a) <= next_double(b);

lemma void prev_double_transitivity_lemma(real a, real b);
    requires a <= b;
    ensures prev_double(a) <= prev_double(b);
   
lemma void next_round_down_lemma(real x, real next_round_down);
    requires next_round_down == next_double(round_down_double(x));
    ensures next_round_down >= x;
    
lemma void prev_round_up_lemma(real x, real prev_round_up);
    requires prev_round_up == prev_double(round_up_double(x));
    ensures prev_round_up <= x;

lemma void next_prev_double_lemma(real x, real nextprev);
    requires nextprev == next_double(prev_double(x));
    ensures nextprev >= x;
    
lemma void prev_next_double_lemma(real x, real prevnext);
    requires prevnext == prev_double(next_double(x));
    ensures prevnext <= x;
    
lemma void prev_double_zero_lemma(real x);
    requires x > 0;
    ensures prev_double(x) >= 0;

fixpoint bool relative_error(real x, real approximation, real epsilon) {
    return x == 0 ? approximation == 0 : approximation <= x + real_abs(epsilon * x) && approximation >= x - real_abs(epsilon * x);
}

//division
fixpoint fp_double double_div(fp_double x, fp_double y){
    switch (x) {
        case real_double(rx): return 
            switch (y) {
    		case real_double(ry): 
    		    return rx == 0 && ry == 0 ? NaN : 
    			rx > 0 && ry == 0 ? pos_inf :
    			rx < 0 && ry == 0 ? neg_inf :
    			rx > 0 && ry > 0 && rx > ry * max_dbl / md_eps ? pos_inf:
    			rx < 0 && ry < 0 && rx < ry * max_dbl / md_eps ? pos_inf:
    			rx > 0 && ry < 0 && rx > ry * min_dbl / md_eps ? neg_inf:
    			rx < 0 && ry > 0 && rx < ry * min_dbl / md_eps ? neg_inf:
    			real_double(23);
        	case pos_inf: return real_double(0);
        	case neg_inf: return real_double(0);
        	case NaN: return NaN;
            };
        case pos_inf: return 
            switch (y) {
    		case real_double(ry): return ry >= 0 ? pos_inf : neg_inf;
        	case pos_inf: return NaN;
        	case neg_inf: return NaN;
        	case NaN: return NaN;
    	    };
        case neg_inf: return 
            switch (y) {
    		case real_double(ry): return ry >= 0 ? neg_inf : pos_inf;
        	case pos_inf: return NaN;
        	case neg_inf: return NaN;
        	case NaN: return NaN;
    	    };
        case NaN: return NaN;
    }
}

fixpoint bool exact_div(fp_double x, fp_double y){
    return double_div(x,y) != real_double(23);
}
//addition
fixpoint fp_double double_add(fp_double x, fp_double y){
    switch (x) {
        case real_double(rx): return 
            switch (y) {
        	case real_double(ry): 
        	    return rx + ry > max_dbl / md_eps ? pos_inf:
        	        rx + ry < min_dbl / md_eps ? neg_inf:
        		real_double(23);
        	case pos_inf: return pos_inf;
        	case neg_inf: return neg_inf;
        	case NaN: return NaN;
            };
        case pos_inf: return 
            switch (y) {
        	case real_double(ry): return pos_inf;
        	case pos_inf: return pos_inf;
        	case neg_inf: return NaN;
        	case NaN: return NaN;
            };
        case neg_inf: return 
            switch (y) {
        	case real_double(ry): return neg_inf;
        	case pos_inf: return NaN;
        	case neg_inf: return neg_inf;
        	case NaN: return NaN;
           };
        case NaN: return NaN;
    }
}

fixpoint bool exact_add(fp_double x, fp_double y){
    return double_add(x,y) != real_double(23);
}

//substraction
fixpoint fp_double double_sub(fp_double x, fp_double y){
     switch (x) {
        case real_double(rx): return 
            switch (y) {
    		case real_double(ry): 
    		    return rx - ry > max_dbl / md_eps ? pos_inf:
    			rx - ry < min_dbl / md_eps ? neg_inf:
    			real_double(23);
        	case pos_inf: return neg_inf;
        	case neg_inf: return pos_inf;
        	case NaN: return NaN;
    	    };
        case pos_inf: return 
            switch (y) {
    		case real_double(ry): return pos_inf;
        	case pos_inf: return NaN;
        	case neg_inf: return pos_inf;
        	case NaN: return NaN;
    	    };
        case neg_inf: return 
            switch (y) {
    		case real_double(ry): return neg_inf;
        	case pos_inf: return neg_inf;
        	case neg_inf: return NaN;
        	case NaN: return NaN;
    	    };
        case NaN: return NaN;
    }
}

fixpoint bool exact_sub(fp_double x, fp_double y){
    return double_sub(x,y) != real_double(23);
}

//multiplication
fixpoint fp_double double_mult(fp_double x, fp_double y){
    switch (x) {
        case real_double(rx): return 
            switch (y) {
    		case real_double(ry): 
    		    return rx * ry > max_dbl / md_eps ? pos_inf:
    			rx * ry < min_dbl / md_eps ? neg_inf:
    			real_double(23);
        	case pos_inf: 
        	    return rx > 0 ? pos_inf:
        	        rx < 0 ? neg_inf:
        	        NaN;
        	case neg_inf: 
        	    return rx > 0 ? neg_inf:
        	        rx < 0 ? pos_inf:
        	        NaN;
        	case NaN: return NaN;
    	    };
        case pos_inf: return 
            switch (y) {
    		case real_double(ry): 
    		    return ry > 0 ? pos_inf:
    		        ry < 0 ? neg_inf:
    		        NaN;
        	case pos_inf: return pos_inf;
        	case neg_inf: return neg_inf;
        	case NaN: return NaN;
    	    };
        case neg_inf: return 
            switch (y) {
    		case real_double(ry): 
    		    return ry > 0 ? neg_inf:
    		        ry < 0 ? pos_inf:
    		        NaN;
        	case pos_inf: return neg_inf;
        	case neg_inf: return pos_inf;
        	case NaN: return NaN;
    	    };
        case NaN: return NaN;
    }
}

fixpoint bool exact_mult(fp_double x, fp_double y){
    return double_mult(x,y) != real_double(23);
}

fixpoint bool real_mult_gt(real a, real b, real c){
    return a * b > c;
}

fixpoint bool bool_eq(bool a, bool b){
    return a == b;
}

fixpoint bool real_mult_round_down(real rx, real ry, real rr){
    return rx * ry < min_dbl || rr >= round_down_double(rx * ry);
}

fixpoint bool real_mult_round_up(real rx, real ry, real rr){
    return rx * ry > max_dbl || rr <= round_up_double(rx * ry);
}
@*/



double vf__double_of_real(real x);
    /*@ requires
    	x > max_dbl * (1 + d_eps) ? ensures fp_of_double(result) == pos_inf :
    	x < min_dbl * (1 + d_eps) ? ensures fp_of_double(result) == neg_inf :
    	ensures fp_of_double(result) == real_double(?rx) &*& 
    	relative_error(x,rx,double_eps) == true;
    @*/
    /*@ ensures true; @*/
    //@ terminates;

double vf__double_of_int(int x);
    //@ requires true;
    //@ ensures fp_of_double(result) == real_double(real_of_int(x));
    //@ terminates;

long double vf__long_double_of_int(int x);
    //@ requires true;
    //@ ensures real_of_long_double(result) == some(real_of_int(x));
    //@ terminates;

double vf__double_of_float(float x);
    //@ requires real_of_float(x) == some(?rx);
    //@ ensures  real_of_double(result) == some(rx);
    //@ terminates;

long double vf__long_double_of_double(double x);
    //@ requires real_of_double(x) == some(?rx);
    //@ ensures real_of_long_double(result) == some(?rresult) &*& rresult == rx;
    //@ terminates;

double vf__double_of_long_double(long double x);
    //@ requires real_of_long_double(x) == some(?rx);
    /*@ ensures real_of_double(result) == some(?rr) &*& 
    relative_error(rx, rr, double_eps) == true;
    @*/
    //@ terminates;

bool vf__double_eq(double x, double y);
    //@ requires true;
    //@ ensures result == (fp_of_double(x) == fp_of_double(y));
    //@ terminates;

bool vf__double_lt(double x, double y);
    //@ requires real_of_double(x) == some(?rx) &*& real_of_double(y) == some(?ry);
    //@ ensures result == (rx < ry);
    //@ terminates;

bool vf__double_le(double x, double y);
    //@ requires real_of_double(x) == some(?rx) &*& real_of_double(y) == some(?ry);
    //@ ensures result == (rx <= ry);
    //@ terminates;

bool vf__double_gt(double x, double y);
    //@ requires real_of_double(x) == some(?rx) &*& real_of_double(y) == some(?ry);
    //@ ensures result == (rx > ry);
    //@ terminates;


bool vf__double_ge(double x, double y);
    //@ requires real_of_double(x) == some(?rx) &*& real_of_double(y) == some(?ry);
    //@ ensures result == (rx >= ry);
    //@ terminates;

double vf__double_add(double x, double y);
    /*@ requires 
    	exact_add(fp_of_double(x), fp_of_double(y)) ? 
    	    ensures fp_of_double(result) == double_add(fp_of_double(x), fp_of_double(y)):
        ensures fp_of_double(x) == real_double(?rx) &*&
        fp_of_double(y) == real_double(?ry) &*&
        switch (fp_of_double(result)) {
            case real_double(rr): return rx + ry > max_dbl ||
        				rr <= round_up_double(rx + ry) &*& 
        				rx + ry < min_dbl ||
        				rr >= round_down_double(rx + ry) &*& 
    					relative_error(rx + ry, rr, double_eps) == true;
    	    case pos_inf: return rx + ry > max_dbl;
    	    case neg_inf: return rx + ry < min_dbl;
    	    case NaN: return false;
    	};
    @*/
    //@ ensures true;
    //@ terminates;



double vf__double_sub(double x, double y);
    /*@ requires 
    	exact_sub(fp_of_double(x),fp_of_double(y)) ? 
    	    ensures fp_of_double(result) == double_sub(fp_of_double(x),fp_of_double(y)) :
    	ensures fp_of_double(x) == real_double(?rx) &*&
    	fp_of_double(y) == real_double(?ry) &*&
    	switch (fp_of_double(result)) {
    	    case real_double(rr): return rx - ry > max_dbl ||
    	    				rr <= round_up_double(rx - ry) &*&
    	    				rx - ry < min_dbl ||
    	    				rr >= round_down_double(rx - ry) &*&
    	    				relative_error(rx - ry, rr, d_eps) == true;
    	    case pos_inf: return rx - ry > max_dbl;
    	    case neg_inf: return rx - ry < min_dbl;
    	    case NaN: return false;
    	};
    @*/
    //@ ensures true;
    //@ terminates;



double vf__double_mul(double x, double y);
    /*@ requires
    	exact_mult(fp_of_double(x), fp_of_double(y)) ? 
    	    ensures fp_of_double(result) == double_mult(fp_of_double(x), fp_of_double(y)):
    	ensures fp_of_double(x) == real_double(?rx) &*&
    	fp_of_double(y) == real_double(?ry) &*& 
    	switch (fp_of_double(result)){
    	    case real_double(rr):
    	        return real_mult_round_up(rx,ry,rr) == true &*&
    	            real_mult_round_down(rx,ry,rr) == true &*&
    	            relative_error(rx * ry, rr, double_eps) == true;
    	    case pos_inf: return real_mult_gt(rx, ry,max_dbl) == true;
    	    case neg_inf: return rx * ry < min_dbl;
    	    case NaN: return false;
    	};
    	@*/
    //@ ensures true;
    //@ terminates;
 



double vf__double_div(double x, double y);
    /*@ requires
        exact_div(fp_of_double(x),fp_of_double(y)) ? 
            ensures fp_of_double(result) == double_div(fp_of_double(x), fp_of_double(y)):
        ensures fp_of_double(x) == real_double(?rx) &*& 
        fp_of_double(y) == real_double(?ry) &*&
        switch (fp_of_double(result)){
            case real_double(rr):
                return real_div(rx,ry) > max_dbl ||
                    rr <= round_up_double(real_div(rx,ry)) &*&
                    real_div(rx,ry) < min_dbl ||
                    rr >= round_down_double(real_div(rx,ry)) &*&
                    relative_error(real_div(rx,ry), rr, double_eps) == true;
            case pos_inf: return real_div(rx,ry) > max_dbl;
            case neg_inf: return real_div(rx,ry) < min_dbl;
            case NaN: return false;
       	};
    @*/
    //@ ensures true;
    //@ terminates;

#endif