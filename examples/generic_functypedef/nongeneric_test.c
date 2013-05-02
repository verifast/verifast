
// sunnyday scenario test for function type declarations without type parameter,
// to test that this does not become broken when adding support
// for function type declarations with type parameter.

/*@
predicate pred<a>(list<a> l);
@*/

typedef void fun_t/*@(int i)@*/();
//@ requires pred<int>(?l);
//@ ensures pred<int>(l);

void fun() //@ : fun_t(nongeneric_test)
//@ requires pred<int>(?l);
//@ ensures pred<int>(l);
{
	
}

void accept_fun_t(fun_t *fun_arg)
//@ requires [_]is_fun_t(fun_arg, nongeneric_test) &*& pred<int>(nil);
//@ ensures pred<int>(nil);
{
	fun_arg();
}

void myfun123()
//@ requires pred<int>(nil);
//@ ensures pred<int>(nil);
{
	//@ produce_function_pointer_chunk fun_t(fun)(nongeneric_test)() { call(); }
	accept_fun_t(fun);
}

