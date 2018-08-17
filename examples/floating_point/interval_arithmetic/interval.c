#ifndef INTERVAL_H
#define INTERVAL_H
#include "stdlib.h"
#include "interval_math.h"



struct interval {
    double a;
    double b;
};
/*@
fixpoint bool leq_double_real(fp_double a, real x){
    switch (a) {
    	case real_double(ra): return ra <= x;
    	case pos_inf: return false;
    	case neg_inf: return true;
    	case NaN: return false;
    }
}

fixpoint bool leq_real_double(real x, fp_double b){
    switch (b) {
    	case real_double(rb): return x <= rb;
    	case pos_inf: return true;
    	case neg_inf: return false;
    	case NaN: return false;
    }
}

fixpoint bool between(fp_double a, fp_double b, real x){
    return leq_double_real(a,x) && leq_real_double(x,b);
}

fixpoint bool is_pos_double(fp_double a){
    switch (a){
        case real_double(ra): return ra >= 0;
        case pos_inf: return true;
        case neg_inf: return false;
        case NaN: return false;
    }
}
    
predicate pos_interval_pred(struct interval *interval, real x) =
    interval->a |-> ?a &*&
    interval->b |-> ?b &*&
    is_pos_double(fp_of_double(a)) == true &*&
    between(fp_of_double(a),fp_of_double(b),x) == true;


predicate interval_pred(struct interval *interval, real x) =
    interval->a |-> ?a &*&
    interval->b |-> ?b &*&
    between(fp_of_double(a),fp_of_double(b),x) == true;
    
lemma void between_lemma(fp_double a, real x, fp_double b)
    requires leq_double_real(a,x) == true &*& leq_real_double(x,b) == true;
    ensures between(a,b,x) == true;
{}
@*/


struct interval *double_add(struct interval *first, struct interval *second)
    /*@ requires interval_pred(first,?x1) &*&
    	interval_pred(second,?x2);@*/
    /*@ ensures interval_pred(first,x1) &*&
        interval_pred(second,x2) &*&
        interval_pred(result,x1 + x2) &*&
    	malloc_block_interval(result); @*/
{
    //@ open interval_pred(first, x1);
    //@ open interval_pred(second, x2);
    //@ assert first->a |-> ?fa;
    //@ assert second->a |-> ?sa;
    //@ assert first->b |-> ?fb;
    //@ assert second->b |-> ?sb;
    struct interval *result = malloc(sizeof(struct interval));
    if (result == 0) { abort(); }
    double l = first->a + second->a;
    result->a = nextafter(l,-INFINITY);
    //@ assert result->a |-> ?ra;
    /*@
    if (is_real_double(fa) == true) {
        assert fp_of_double(fa) == real_double(?rfa);
        if (is_real_double(sa) == true) {
            assert fp_of_double(sa) == real_double(?rsa);
            if (is_real_double(l)) {
                assert fp_of_double(l) == real_double(?rl);
            	assert rl <= round_up_double(rfa + rsa) || rfa + rsa > max_dbl;
        	if (is_real_double(ra)) {
    	    	    if (rl <= round_up_double(rfa + rsa)){
    	    	        assert fp_of_double(ra) == real_double(?rra);
    	    	        assert rra == prev_double(rl);
    	    	        prev_double_transitivity_lemma(rl,round_up_double(rfa + rsa));
    	    	        assert rra <= prev_double(round_up_double(rfa + rsa));
    	    	        prev_round_up_lemma(rfa + rsa, prev_double(round_up_double(rfa + rsa)));
    	    	        assert leq_double_real(fp_of_double(ra), x1 + x2) == true;
    	    	    } else {
    	    	        assert rfa + rsa > max_dbl;
    	    	        assert fp_of_double(ra) == real_double(?rra);
    	    	        assert rl >= round_down_double(rfa + rsa);
    	    	        round_down_max_dbl_lemma(rfa + rsa);
    	    	        assert rl >= max_dbl;
    	    	        real_double_lemma(l);
    	    	        assert rl == max_dbl;
    	    	        assert rra == prev_double(rl);
    	    	        prev_double_lemma(rl, rra);
    	    	        assert leq_double_real(fp_of_double(ra), x1 + x2) == true;
    	    	    }
    	    	}
    	    	assert x1 + x2 >= rfa + rsa;
    	    } else {}
    	    assert leq_double_real(fp_of_double(ra), x1 + x2) == true;
        } else {}
    } else if (fp_of_double(fa) == neg_inf){
        if (is_real_double(sa) == true) {
            assert fp_of_double(sa) == real_double(?rsa); // zonder deze assert geen succesvolle verificatie.
    	} else {}
    } else {}
    @*/
    //@ assert leq_double_real(fp_of_double(ra), x1 + x2) == true;
    double u = first->b + second->b;
    result->b = nextafter(u,INFINITY);
    //@ assert result->b |-> ?rb;
    /*@
    if (is_real_double(fb) == true) {
        assert fp_of_double(fb) == real_double(?rfb);
        real_double_lemma(fb);
        if (is_real_double(sb) == true) {
            assert fp_of_double(sb) == real_double(?rsb);
    	    if (!is_real_double(u)) {
    	    } else {
    	        assert fp_of_double(u) == real_double(?ru);
    	        assert x1 <= rfb;
    	        assert x2 <= rsb;
    	        assert x1 + x2 <= rfb + rsb;
    	        assert ru >= round_down_double(rfb + rsb) || rfb + rsb < min_dbl;
    	        if (is_real_double(rb)) {
    	            if (ru >= round_down_double(rfb + rsb)) {       
    	    	        assert fp_of_double(rb) == real_double(?rrb);
    	    	        assert rrb == next_double(ru);
    	    	        next_double_transitivity_lemma(round_down_double(rfb + rsb), ru);
    	    	        assert next_double(ru) >= next_double(round_down_double(rfb + rsb));
    	    	        assert rrb == next_double(ru);
    	    	        leq_transitivity_lemma(next_double(round_down_double(rfb + rsb)), next_double(ru), rrb);
    	    	        assert rrb  >= next_double(round_down_double(rfb + rsb));
    	    	        next_round_down_lemma(rfb + rsb, next_double(round_down_double(rfb + rsb)));
    	    	        assert x1 + x2 <= rrb;
    	    	        assert leq_real_double(x1 + x2, fp_of_double(rb)) == true;
    	    	    } else { 
    	    	        assert rfb + rsb < min_dbl;
    	    	        assert rfb + rsb >= min_dbl / md_eps;
    	    	        assert fp_of_double(rb) == real_double(?rrb);
    	    	        assert ru <= round_up_double(rfb + rsb);
    	    	        round_up_min_dbl_lemma(rfb + rsb);
    	    	        assert ru <= min_dbl;
    	    	        real_double_lemma(u);
    	    	        assert ru == min_dbl;
    	    	        assert rrb == next_double(ru);
    	    	        next_double_lemma(ru, rrb);
    	    	        assert x1 + x2 <= rrb;
    	    	        assert leq_real_double(x1 + x2, fp_of_double(rb)) == true;
    	    	    }
    	        } else {
        	    assert fp_of_double(rb) == pos_inf;
    	    	    assert leq_real_double(x1 + x2, fp_of_double(rb)) == true;
    	    	}
    	    	assert x1 + x2 <= rfb + rsb;
    	    	assert leq_real_double(x1 + x2, fp_of_double(rb)) == true;
    	    }
        } else {}
    } else if (fp_of_double(fb) == pos_inf){
        if (is_real_double(sb) == true) {
            assert fp_of_double(sb) == real_double(?rsb); //Nodig voor verificatie
        } else {}
    } else {}
    @*/
    //@ assert leq_real_double(x1 + x2, fp_of_double(rb)) == true;
    return result;
    //@ close(interval_pred(result,x1 + x2));
    //@ close(interval_pred(first,x1));
    //@ close(interval_pred(second,x2));
}

struct interval *double_sub(struct interval *first, struct interval *second)
    /*@ requires interval_pred(first,?x1) &*&
    	interval_pred(second,?x2); @*/
    /*@ ensures interval_pred(first,x1) &*&
    	interval_pred(second,x2) &*&
    	interval_pred(result,x1 - x2) &*&
    	malloc_block_interval(result); @*/
{
    //@ open interval_pred(first, x1);
    //@ open interval_pred(second, x2);
    //@ assert first->a |-> ?fa;
    //@ assert second->a |-> ?sa;
    //@ assert first->b |-> ?fb;
    //@ assert second->b |-> ?sb;
    struct interval *result = malloc(sizeof(struct interval));
    if (result == 0) { abort(); }
    double l = first->a - second->b;
    result->a = nextafter(l,-INFINITY);
    //@ assert result->a |-> ?ra;
    /*@
    if (is_real_double(fa) == true) {
        assert fp_of_double(fa) == real_double(?rfa);
        if (is_real_double(sb) == true) {
            assert fp_of_double(sb) == real_double(?rsb);
            if (is_real_double(l)) {
                assert fp_of_double(l) == real_double(?rl);
        	assert rl <= round_up_double(rfa - rsb) || rfa - rsb > max_dbl;
    	    	if (is_real_double(ra)) {
    	    	    if (rl <= round_up_double(rfa - rsb)){
    	    	        assert fp_of_double(ra) == real_double(?rra);
    	    	        assert rra == prev_double(rl);
    	    	        prev_double_transitivity_lemma(rl,round_up_double(rfa - rsb));
    	    	        assert rra <= prev_double(round_up_double(rfa - rsb));
    	    	        prev_round_up_lemma(rfa - rsb, prev_double(round_up_double(rfa - rsb)));
    	    	        assert leq_double_real(fp_of_double(ra), x1 - x2) == true;
    	    	    } else {
    	    	        assert rfa - rsb > max_dbl;
    	    	        assert fp_of_double(ra) == real_double(?rra);
    	    	        assert rl >= round_down_double(rfa - rsb);
    	    	        round_down_max_dbl_lemma(rfa - rsb);
    	    	        assert rl >= max_dbl;
    	    	        real_double_lemma(l);
    	    	        assert rl == max_dbl;
    	    	        assert rra == prev_double(rl);
    	    	        prev_double_lemma(rl, rra);
    	    	        assert leq_double_real(fp_of_double(ra), x1 - x2) == true;
    	    	    }
    	    	}
    	    } else {}    
    	} else {}
    } else if (fp_of_double(fa) == neg_inf){
        if (is_real_double(sb) == true) {
            real_double_lemma(sb);
        } else {}
    } else {}
    @*/
    //@ assert leq_double_real(fp_of_double(ra), x1 - x2) == true;
    double u = first->b - second->a;
    result->b = nextafter(u,INFINITY);
    //@ assert result->b |-> ?rb;
    /*@
    if (is_real_double(fb) == true) {
        assert fp_of_double(fb) == real_double(?rfb);
        real_double_lemma(fb);
        if (is_real_double(sa) == true) {
            assert fp_of_double(sa) == real_double(?rsa);
    	    if (is_real_double(u)) {
    	        assert fp_of_double(u) == real_double(?ru);
    	        assert ru >= round_down_double(rfb - rsa) || rfb - rsa < min_dbl;
    	        if (is_real_double(rb)) {
    	            if (ru >= round_down_double(rfb - rsa)) {
    	    	        assert fp_of_double(rb) == real_double(?rrb);
    	    	        assert rrb == next_double(ru);
    	    	        next_double_transitivity_lemma(round_down_double(rfb - rsa), ru);
    	    	        assert next_double(ru) >= next_double(round_down_double(rfb - rsa));
    	    	        assert rrb == next_double(ru);
    	    	        leq_transitivity_lemma(next_double(round_down_double(rfb - rsa)), next_double(ru), rrb);
    	    	        assert rrb  >= next_double(round_down_double(rfb - rsa));
    	    	        next_round_down_lemma(rfb - rsa, next_double(round_down_double(rfb - rsa)));
    	    	        assert x1 - x2 <= rrb;
    	    	        assert leq_real_double(x1 - x2, fp_of_double(rb)) == true;
    	    	    } else { 
    	    	        assert rfb - rsa < min_dbl;
    	    	        assert rfb - rsa >= min_dbl / md_eps;
    	    	        assert fp_of_double(rb) == real_double(?rrb);
    	    	        assert ru <= round_up_double(rfb  - rsa);
    	    	        round_up_min_dbl_lemma(rfb - rsa);
    	    	        assert ru <= min_dbl;
    	    	        real_double_lemma(u);
    	    	        assert ru == min_dbl;
    	    	        assert rrb == next_double(ru);
    	    	        next_double_lemma(ru, rrb);
    	    	        assert leq_real_double(x1 - x2, fp_of_double(rb)) == true;
    	    	    }
    	    	    assert leq_real_double(x1 - x2, fp_of_double(rb)) == true;
    	    	} else {}
    	    } else {}
    	    assert leq_real_double(x1 - x2, fp_of_double(rb)) == true;
    	} else {}
    } else if (fp_of_double(fb) == pos_inf){
        if (is_real_double(sa) == true) {
            real_double_lemma(sa);
    	} else {}
    } else if (fp_of_double(fb) == neg_inf){
    } else {}
    @*/
    //@ assert leq_real_double(x1 - x2, fp_of_double(rb)) == true;
    //@ close(interval_pred(result,x1 - x2));
    //@ close(interval_pred(first,x1));
    //@ close(interval_pred(second,x2));
    return result;
}


struct interval *double_mult(struct interval *first, struct interval *second)
    /*@ requires pos_interval_pred(first,?x1) &*&
    	pos_interval_pred(second,?x2);@*/
    /*@ ensures pos_interval_pred(first,x1) &*&
    	pos_interval_pred(second,x2) &*&
    	pos_interval_pred(result, x1 * x2) &*&
    	malloc_block_interval(result); @*/
    {
    //@ open pos_interval_pred(first,x1);
    //@ open pos_interval_pred(second,x2);
    struct interval *result = malloc(sizeof(struct interval));
    if (result == 0) { abort(); }
    //@ real_of_int_lemma_UNSAFE(0,0);
    //@ assert first->a |-> ?fa;
    //@ assert first->b |-> ?fb;
    //@ assert second->a |-> ?sa;
    //@ assert second->b |-> ?sb;
    
    
    
    double l = first->a * second->a;
    if (isnan(l)){l = 0;}
    if (l == 0) {
        result->a = 0;
    } else {
        result->a = nextafter(l,-INFINITY);
    }
    //@ assert result->a |-> ?ra;
    //@ assert is_real_double(fa) || fp_of_double(fa) == pos_inf;
    /*@

    switch (fp_of_double(fa)){
        case real_double(rfa):
            switch (fp_of_double(sa)){
                case real_double(rsa):
                    if (fp_of_double(l) == pos_inf){
                        assert real_mult_gt(rfa,rsa,max_dbl) == true;
                        real_mult_gt_lemma(rfa,rsa,max_dbl);
                        assert rfa * rsa > max_dbl;
                        assert x1 >= rfa;
                        assert x2 >= rsa;
                        assert rfa >= 0;
                        assert rsa >= 0;
                        mult_leq_substitution(rfa,rsa,x1,x2);
                        assert x1 * x2 >= rfa * rsa;
                        leq_transitivity_lemma(max_dbl,rfa * rsa, x1 * x2);
                        assert x1 * x2 >= max_dbl;
                        assert fp_of_double(ra) == real_double(?rra);
                        assert fp_of_double(ra) == double_nextafter(fp_of_double(l),neg_inf);
                        assert rra == max_dbl;
                    } else {
                        assert fp_of_double(l) == real_double(?rl);
                        assert fp_of_double(ra) == real_double(?rra);
                        if (rra == 0){
                            assert x1 >= 0;
                            assert x2 >= 0;
                            product_sign_lemma(x1,x2);
                            assert x1 * x2 >= 0;
                            assert leq_double_real(fp_of_double(ra), x1 * x2) == true;
                        } else {
                            assert rra == prev_double(rl);
                            assert real_mult_round_up(rfa,rsa,rl) == true;
                            real_mult_round_up_lemma(rfa,rsa,rl);
                            assert rl <= round_up_double(rfa * rsa) || rfa * rsa > max_dbl;
                            if (rfa * rsa > max_dbl){
                                real_mult_round_down_lemma(rfa,rsa,rl);
                                assert rl >= round_down_double(rfa * rsa);
                                round_down_max_dbl_lemma(rfa * rsa);
                                real_double_lemma(l);
                                assert rl == max_dbl;
                                assert rra == prev_double(rl);
                                prev_double_lemma(rl,rra);
                                assert rra < max_dbl;
                                assert x1 * x2 >= rfa * rsa;
                                leq_transitivity_lemma(max_dbl, rfa * rsa, x1* x2);
                                assert x1 * x2 >= max_dbl;
                                
                            } else {
                                prev_double_transitivity_lemma(rl,round_up_double(rfa * rsa));
                                prev_round_up_lemma(rfa * rsa, prev_double(round_up_double(rfa * rsa)));
                                assert rra <= rfa * rsa;
                                assert rfa * rsa > 0;
                                if (rl == 0){
                                    assert rra == 0;
                                } else {
                                    assert rl > 0;
                                    prev_double_zero_lemma(rl);
                                    assert rra >= 0;
                                }
                            }
                        }
                        
                    }
                case pos_inf: assert false;
                case neg_inf: assert false;
                case NaN: assert false;
            }
        case pos_inf: assert false;
        case neg_inf: assert false;
        case NaN: assert false;
    
    }
    @*/
    //@ assert is_pos_double(fp_of_double(ra)) == true;
    //@ assert leq_double_real(fp_of_double(ra), x1 * x2) == true;
    double u = first->b * second->b;
    if (isnan(u)){
        result->b = 0;
    } else {
        result->b = nextafter(u,INFINITY);
    }
    //@ assert result->b |-> ?rb;
    /*@

    switch (fp_of_double(fb)){
        case real_double(rfb):
            switch (fp_of_double(sb)){
                case real_double(rsb):
                    if (fp_of_double(u) == pos_inf){
                        assert real_mult_gt(rfb,rsb,max_dbl) == true;
                        real_mult_gt_lemma(rfb,rsb,max_dbl);
                        assert rfb * rsb > max_dbl;
                    } else {
                        assert rfb >= 0;
                        assert rsb >= 0;
                        assert fp_of_double(u) == real_double(?ru);
                        assert x1 <= rfb;
                        assert x2 <= rsb;
                        assert x1 >= 0;
                        assert x2 >= 0;
                        mult_leq_substitution(x1,x2,rfb,rsb);
                        assert x1 * x2 <= rfb * rsb;
                        if (fp_of_double(rb) == pos_inf){
                            assert ru == max_dbl;
                        } else {
                            assert fp_of_double(rb) == real_double(?rrb);
                            assert rrb == next_double(ru);
                            assert real_mult_round_down(rfb,rsb,ru) == true;
                            real_mult_round_down_lemma(rfb,rsb,ru);
                            assert ru >= round_down_double(rfb * rsb);
                            next_double_transitivity_lemma(round_down_double(rfb * rsb), ru);
                            assert rfb >= 0;
                            assert rsb >= 0;
                            next_round_down_lemma(rfb * rsb, next_double(round_down_double(rfb * rsb)));
                            assert rrb >= rfb * rsb;
                        }
                    }
                case pos_inf: 
                    assert fp_of_double(u) == pos_inf || fp_of_double(rb) == real_double(0);
                    assert fp_of_double(rb) == pos_inf || fp_of_double(rb) == real_double(0);
                    if (fp_of_double(rb) == real_double(0)){
                        assert x1 == 0;
                        strict_product_sign_lemma(x1,x2);
                        assert x1 * x2 == 0;
                    } else {}
                    assert leq_real_double(x1 * x2, fp_of_double(rb)) == true;
                case neg_inf: assert false;
                case NaN: assert false;
            }
        case pos_inf:
            switch (fp_of_double(sb)){
                case real_double(rsb):
                    assert fp_of_double(rb) == pos_inf || fp_of_double(rb) == real_double(0);
                    if (fp_of_double(rb) == real_double(0)){
                        assert x2 == 0;
                        strict_product_sign_lemma(x1,x2);
                        assert x1 * x2 == 0;
                    } else {}
                    assert leq_real_double(x1 * x2, fp_of_double(rb)) == true;
                case pos_inf:
                    assert leq_double_real(fp_of_double(ra), x1 * x2) == true;
                case neg_inf: assert false;
                case NaN: assert false;
            }
        case neg_inf: assert false;
        case NaN: assert false;
    
    }
    @*/
    /*@

    switch (fp_of_double(fa)){
        case real_double(rfa):
            switch (fp_of_double(sa)){
                case real_double(rsa):
                    if (fp_of_double(l) == pos_inf){
                        assert real_mult_gt(rfa,rsa,max_dbl) == true;
                        real_mult_gt_lemma(rfa,rsa,max_dbl);
                        assert rfa * rsa > max_dbl;
                        assert x1 >= rfa;
                        assert x2 >= rsa;
                        assert rfa >= 0;
                        assert rsa >= 0;
                        mult_leq_substitution(rfa,rsa,x1,x2);
                        assert x1 * x2 >= rfa * rsa;
                        leq_transitivity_lemma(max_dbl,rfa * rsa, x1 * x2);
                        assert x1 * x2 >= max_dbl;
                        assert fp_of_double(ra) == real_double(?rra);
                        assert fp_of_double(ra) == double_nextafter(fp_of_double(l),neg_inf);
                        assert rra == max_dbl;
                    } else {
                        assert fp_of_double(l) == real_double(?rl);
                        assert fp_of_double(ra) == real_double(?rra);
                        if (rra == 0){
                            assert x1 >= 0;
                            assert x2 >= 0;
                            product_sign_lemma(x1,x2);
                            assert x1 * x2 >= 0;
                            assert leq_double_real(fp_of_double(ra), x1 * x2) == true;
                        } else {
                            assert rra == prev_double(rl);
                            assert real_mult_round_up(rfa,rsa,rl) == true;
                            real_mult_round_up_lemma(rfa,rsa,rl);
                            assert rl <= round_up_double(rfa * rsa) || rfa * rsa > max_dbl;
                            if (rfa * rsa > max_dbl){
                                real_mult_round_down_lemma(rfa,rsa,rl);
                                assert rl >= round_down_double(rfa * rsa);
                                round_down_max_dbl_lemma(rfa * rsa);
                                real_double_lemma(l);
                                assert rl == max_dbl;
                                assert rra == prev_double(rl);
                                prev_double_lemma(rl,rra);
                                assert rra < max_dbl;
                                mult_leq_substitution(rfa,rsa,x1,x2);
                                assert x1 * x2 >= rfa * rsa;
                                leq_transitivity_lemma(max_dbl, rfa * rsa, x1* x2);
                                assert x1 * x2 >= max_dbl;
                                
                            } else {
                                prev_double_transitivity_lemma(rl,round_up_double(rfa * rsa));
                                prev_round_up_lemma(rfa * rsa, prev_double(round_up_double(rfa * rsa)));
                                assert rra <= rfa * rsa;
                                assert rfa * rsa > 0;
                                mult_leq_substitution(rfa,rsa,x1,x2);
                                assert x1 * x2 >= rfa * rsa;
                                leq_transitivity_lemma(rra,rfa*rsa,x1*x2);
                                assert x1 * x2 >= rra;
                                assert rra <= x1 * x2;
				assert leq_double_real(fp_of_double(ra), x1 * x2) == true;
                                if (rl == 0){
                                    assert rra == 0;
                                } else {
                                    assert rl > 0;
                                    prev_double_zero_lemma(rl);
                                    assert rra >= 0;
                                    assert x1 * x2 >= rfa * rsa;
                                    assert x1 * x2 >= rra;
                                    assert rra <= x1 * x2;
                                    assert leq_double_real(fp_of_double(ra), x1 * x2) == true;
                                }
                            }
                        }
                        
                    }
                case pos_inf: assert false;
                case neg_inf: assert false;
                case NaN: assert false;
            }
        case pos_inf: assert false;
        case neg_inf: assert false;
        case NaN: assert false;
    
    }
    @*/

    //@ assert leq_double_real(fp_of_double(ra), x1 * x2) == true;
    //@ assert leq_real_double(x1 * x2, fp_of_double(rb)) == true;
    //@ assert leq_double_real(fp_of_double(ra), x1 * x2) == true;
    //@ between_lemma(fp_of_double(ra),x1 * x2, fp_of_double(rb));
    //@ assert is_pos_double(fp_of_double(ra)) == true;

    //@ close(pos_interval_pred(result,x1 * x2));
    //@ close(pos_interval_pred(first,x1));
    //@ close(pos_interval_pred(second,x2));
    return result;
}


struct interval *double_div(struct interval *first, struct interval *second)
    /*@ requires pos_interval_pred(first,?x1) &*&
        pos_interval_pred(second,?x2) &*&
        x2 != 0;
    @*/
    /*@ ensures pos_interval_pred(first,x1) &*&
    	pos_interval_pred(second,x2) &*&
    	pos_interval_pred(result, real_div(x1, x2)) &*&
    	malloc_block_interval(result);
    @*/
{
    //@ open pos_interval_pred(first,x1);
    //@ open pos_interval_pred(second,x2);
    //@ assert first->a |-> ?fa;
    //@ assert first->b |-> ?fb;
    //@ assert second->a |-> ?sa;
    //@ assert second->b |-> ?sb;
    //@ real_of_int_lemma_UNSAFE(0,0);
    struct interval *result = malloc(sizeof(struct interval));
    if (result == 0) { abort(); }
    double l = first->a / second->b;
    if (l == 0){
        result->a = 0;
        //@ assert result->a |-> ?ra;
        //@ assert fp_of_double(sa) == real_double(?rsa);
        //@ assert fp_of_double(fa) == real_double(?rfa);
        //@ assert x1 >= 0;
        //@ assert x2 >= 0;
        //@ real_div_pos_lemma(x1,x2);
        //@ assert real_div(x1,x2) >= 0;
        
     } else {
        result->a = nextafter(l, -INFINITY);
        //@ assert result->a |-> ?ra;	    
        //@ assert fp_of_double(fa) == real_double(?rfa);
        //@ assert fp_of_double(sa) == real_double(?rsa);
        /*@
        if (fp_of_double(sb) == pos_inf){     
        } else {
            assert fp_of_double(sb) == real_double(?rsb);
            if (fp_of_double(l) == pos_inf) {
               assert fp_of_double(ra) == real_double(max_dbl);
               assert fp_of_double(l) == double_div(fp_of_double(fa),fp_of_double(sb)) || real_div(rfa,rsb) > max_dbl;
               assert fp_of_double(l) == double_div(real_double(rfa),real_double(rsb)) || real_div(rfa,rsb) > max_dbl;
               real_div_lemma(rfa,rsb,real_div(rfa,rsb));
               if (real_div(rfa,rsb) > max_dbl){          
                   cancellation_lemma2(rsb,max_dbl,real_div(rfa,rsb));
               }
               assert rfa > rsb * max_dbl;
               if (rsb == 0){
                   assert fp_of_double(sa) == real_double(?rsa);
                   assert rsa == 0;
                   assert x2 == 0;
                   assert false;
               }
               assert rsb > 0;
               assert x2 != 0;
               if (x2 < 0){
                   assert fp_of_double(sa) == real_double(?rsa);
                   assert false;
               } //neccesary to prove next line
               assert x2 > 0;
               real_div_lemma(rfa,rsb,real_div(rfa,rsb));
               assert rfa == rsb * real_div(rfa,rsb);
               assert rsb * real_div(rfa,rsb) > rsb * max_dbl;
               cancellation_lemma(rsb,max_dbl,real_div(rfa,rsb));
               assert real_div(rfa,rsb) >= max_dbl;
               division_lemma(rfa,x2,rsb);
               division_lemma2(x2,rfa,x1);
               assert real_div(x1,x2) >= max_dbl;
               real_div_pos_lemma(rfa,rsb);
            } else if (fp_of_double(ra) == neg_inf){
                if (fp_of_double(l) == neg_inf){
                    assert real_div(rfa,rsb) <= min_dbl;
                    real_div_pos_lemma(rfa,rsb);
                    assert false;
                } else {
                    assert fp_of_double(l) == real_double(min_dbl);
                    real_div_pos_lemma(rfa,rsb);
                    assert false;
                }
            } else {
                assert fp_of_double(l) == real_double(?rl);
                assert fp_of_double(ra) == real_double(?rra);
                assert rra == prev_double(rl);
                assert rl <= round_up_double(real_div(rfa,rsb)) || real_div(rfa,rsb) > max_dbl;
                assert rl >= round_down_double(real_div(rfa,rsb)) || real_div(rfa,rsb) < min_dbl;
                if (real_div(rfa,rsb) > max_dbl){
                    round_down_max_dbl_lemma(real_div(rfa,rsb));
                    real_double_lemma(l);
                    assert rl == max_dbl;
                    prev_double_lemma(rl,rra);
                    assert real_div(rfa,rsb) >= rra;
                    division_lemma(rfa,x2,rsb);
                    division_lemma2(x2,rfa,x1);      
                } else {
                    assert rl <= round_up_double(real_div(rfa,rsb));
                    prev_double_transitivity_lemma(rl,round_up_double(real_div(rfa,rsb)));
                    prev_round_up_lemma(real_div(rfa,rsb), prev_double(round_up_double(real_div(rfa,rsb))));
                    assert rra <= real_div(rfa,rsb);
                    division_lemma(rfa,x2,rsb);
                    division_lemma2(x2,rfa,x1);
                    //now proof that rra >= 0
                    assert rl >= round_down_double(real_div(rfa,rsb)) || real_div(rfa,rsb) < min_dbl;
                    real_div_pos_lemma(rfa,rsb);
                    assert rl >= round_down_double(real_div(rfa,rsb));
                    assert rl > 0;
                    prev_double_zero_lemma(rl);
                }
            }  
        }
        @*/
    }
    //@ assert result->a |-> ?ra;
    //@ assert leq_double_real(fp_of_double(ra), real_div(x1, x2)) == true;
    //@ assert is_pos_double(fp_of_double(ra)) == true;
    double u = first->b / second->a;
    if (isnan(u)){
        result->b = 0;
        //@ assert result->b |-> ?rb;
        //@ assert fp_of_double(fa) == real_double(?rfa);
        //@ assert fp_of_double(sa) == real_double(?rsa);
        //@ assert fp_of_double(fb) == real_double(?rfb);
        //@ assert rfb == 0;
        //@ assert rsa == 0;
        //@ assert rfa == 0;
        //@ assert x1 == 0;
        //@ assert x2 > 0;
        //@ real_div_lemma(x1,x2,real_div(x1,x2));
        //@ assert real_div(x1,x2) == 0;
        //@ assert leq_real_double(real_div(x1, x2), fp_of_double(rb)) == true;
    } else {
        result->b = nextafter(u, INFINITY);
        //@ assert result->b |-> ?rb;
        //@ assert fp_of_double(sa) == real_double(?rsa);
        /*@
        if (fp_of_double(fb) == pos_inf){
        
        } else {
            assert fp_of_double(fb) == real_double(?rfb);
            if (fp_of_double(u) == pos_inf){
            } else if (fp_of_double(u) == neg_inf){
                assert real_div(rfb,rsa) <= min_dbl;
                real_div_lemma(rfb,rsa,real_div(rfb,rsa));
                assert false;
            } else {
                assert fp_of_double(u) == real_double(?ru);
                if (fp_of_double(rb) == pos_inf){
                    assert ru == max_dbl;
                } else {
                    assert fp_of_double(rb) == real_double(?rrb);
                    real_div_lemma(rfb,rsa,real_div(rfb,rsa));
                    assert ru >= round_down_double(real_div(rfb,rsa));
                    assert rrb == next_double(ru);
                    next_double_transitivity_lemma(round_down_double(real_div(rfb,rsa)),ru);
                    assert rrb >= next_double(round_down_double(real_div(rfb,rsa)));
                    next_round_down_lemma(real_div(rfb,rsa),next_double(round_down_double(real_div(rfb,rsa))));
                    assert rrb >= real_div(rfb,rsa);
                    division_lemma(rfb,rsa,x2);
                    assert rrb >= real_div(rfb,x2);
                    division_lemma2(x2,x1,rfb);
                    assert rrb >= real_div(x1,x2);   
                }
            }
        }
        @*/  
        //@ assert leq_real_double(real_div(x1, x2), fp_of_double(rb)) == true;
    }
    //@ assert result->b |-> ?rb;
    //@ assert leq_double_real(fp_of_double(ra), real_div(x1, x2)) == true;
    //@ assert leq_real_double(real_div(x1, x2), fp_of_double(rb)) == true;
    //@ assert is_pos_double(fp_of_double(ra)) == true;
    //@ close(pos_interval_pred(result,real_div(x1, x2)));
    //@ close(pos_interval_pred(first,x1));
    //@ close(pos_interval_pred(second,x2));
    return result;
}

#endif
