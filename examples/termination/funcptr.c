#include <stdlib.h>
//@ #include "termination.gh"

struct int_func_object {
    int_func *invoke;
    //@ predicate(int_func_object, list<void *>) p;
};
typedef struct int_func_object *int_func_object;

typedef int int_func/*@(predicate(int_func_object, list<void *>) p)@*/(int_func_object object, int x);
    //@ requires [?f]int_func_object(object, this, p, ?d) &*& call_perm(currentThread, d);
    //@ ensures [f]int_func_object(object, this, p, d);
    //@ terminates;

/*@

predicate int_func_object(int_func_object object, void *invoke, predicate(int_func_object, list<void *>) p, list<void *> d) =
    object->invoke |-> invoke &*&
    object->p |-> p &*&
    [_]is_int_func(invoke, p) &*&
    p(object, ?d_) &*&
    bag_le(func_lt, cons(invoke, d_), d) == true;

@*/

int int_func_object_invoke(int_func_object object, int x)
    //@ requires [?f]int_func_object(object, _, _, ?d) &*& call_perm_below(currentThread, ?d1) &*& bag_lt(func_lt, cons(int_func_object_invoke, d), d1) == true;
    //@ ensures [f]int_func_object(object, _, _, d);
    //@ terminates;
{
    //@ call_perm(cons(int_func_object_invoke, d));
    //@ call_perm_below(2);
    //@ bag_lt_xs_cons_xs(func_lt, int_func_object_invoke, d);
    //@ open [f]int_func_object(object, _, ?p, d);
    //@ assert [f]p(object, ?d_);
    int_func *invoke = object->invoke;
    //@ close [f]int_func_object(object, invoke, p, d);
    //@ is_order_func_lt();
    //@ bag_le_cons_xs_cons_ys(func_lt, invoke, nil, d_);
    //@ bag_le_bag_lt(func_lt, cons(invoke, d_), d, cons(int_func_object_invoke, d));
    //@ bag_le_bag_lt(func_lt, {invoke}, cons(invoke, d_), cons(int_func_object_invoke, d));
    //@ consume_call_perm_for(invoke);
    //@ call_perm(d);
    return invoke(object, x);
}

/*@

predicate plus_one(int_func_object object, list<void *> d) =
    malloc_block_int_func_object(object);

@*/

int plus_one(int_func_object object, int x)
    //@ requires [?f]int_func_object(object, plus_one, @plus_one, ?d) &*& call_perm(currentThread, d);
    //@ ensures [f]int_func_object(object, plus_one, @plus_one, d);
    //@ terminates;
{
    //@ leak call_perm(currentThread, d);
    return x + 1;
}

int_func_object create_plus_one()
    //@ requires call_perm_below(currentThread, ?d) &*& bag_lt(func_lt, {create_plus_one}, d) == true;
    //@ ensures int_func_object(result, _, _, {create_plus_one});
    //@ terminates;
{
    int_func_object fObj = malloc(sizeof(struct int_func_object));
    if (fObj == 0) abort();
    fObj->invoke = plus_one;
    //@ fObj->p = @plus_one;
    //@ produce_function_pointer_chunk int_func(plus_one)(@plus_one)(object, x) { call(); }
    //@ close plus_one(fObj, nil);
    return fObj;
    //@ close int_func_object(fObj, plus_one, @plus_one, {create_plus_one});
    //@ leak call_perm_below(currentThread, _);
}

struct twice_data {
    struct int_func_object object;
    int_func_object f;
};

/*@

predicate twice(int_func_object object, list<void *> d) =
    twice_data_f((void *)object, ?f) &*& int_func_object(f, _, _, d);

@*/

int twice(int_func_object object, int x)
    //@ requires [?frac]int_func_object(object, twice, @twice, ?d) &*& call_perm(currentThread, d);
    //@ ensures [frac]int_func_object(object, twice, @twice, d);
    //@ terminates;
{
    //@ open int_func_object(_, _, _, _);
    //@ open twice(_, ?df);
    //@ call_perm_weaken(cons(twice, df));
    struct twice_data *twiceData = (void *)object;
    int_func_object fObj = twiceData->f;
    //@ call_perm_below(1);
    //@ is_order_func_lt();
    //@ bag_lt_cons_lt(func_lt, int_func_object_invoke, twice, df);
    int y = int_func_object_invoke(fObj, x);
    return 2 * y;
    //@ close [frac]twice(object, df);
    //@ close [frac]int_func_object(object, twice, @twice, d);
}

int_func_object create_twice(int_func_object fObj)
    //@ requires int_func_object(fObj, _, _, ?d_fObj) &*& call_perm_below(currentThread, ?d) &*& bag_lt(func_lt, cons(create_twice, d_fObj), d) == true;
    //@ ensures int_func_object(result, _, _, cons(create_twice, d_fObj));
    //@ terminates;
{
    //@ call_perm(cons(create_twice, d_fObj));
    struct twice_data *obj = malloc(sizeof(struct twice_data));
    if (obj == 0) abort();
    obj->object.invoke = twice;
    obj->f = fObj;
    //@ is_order_func_lt();
    //@ bag_lt_cons_lt(func_lt, twice, create_twice, d_fObj);
    //@ int_func_object object = (void *)obj;
    return (void *)obj;
    //@ object->p = @twice;
    //@ produce_function_pointer_chunk int_func(twice)(@twice)(object_, x) { call(); }
    //@ close twice(object, d_fObj);
    //@ close int_func_object((void *)obj, twice, @twice, cons(create_twice, d_fObj));
    //@ leak call_perm(currentThread, _);
    //@ leak malloc_block_twice_data(obj);
}

int main() //@ : main
    //@ requires true;
    //@ ensures true;
    //@ terminates;
{
    //@ produce_call_below_perm_();
    //@ call_below_perm__elim(main);
    //@ produce_call_below_perm_();
    //@ call_below_perm__elim(main);
    //@ produce_call_below_perm_();
    //@ call_below_perm__elim(main);
    //@ produce_call_below_perm_();
    //@ call_below_perm__elim(main);
    
    int_func_object plusOne = create_plus_one();
    int_func_object twicePlusOne = create_twice(plusOne);
    int_func_object twiceTwicePlusOne = create_twice(twicePlusOne);
    //@ merge_fractions call_perm_below(currentThread, {main});
    int_func_object_invoke(twiceTwicePlusOne, 10);
    //@ leak int_func_object(twiceTwicePlusOne, _, _, _);
    return 0;
}