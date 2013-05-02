
// sunny day scenario

/*@
predicate pred<a>(list<a> l);
@*/

void fun2();
//@ requires true;
//@ ensures true;

typedef void fun_t/*@<a>(void *smth)@*/(int i);
//@ requires pred<a>(?l);
//@ ensures pred<a>(l);

void fun(int i)
//@ : fun_t<int>(fun2)
//@ requires pred<int>(?l);
//@ ensures pred<int>(l);
{
}

void accept_fun_t_int(fun_t *fun_t_arg)
//@ requires [_]is_fun_t<int>(fun_t_arg, fun2) &*& pred<int>(nil);
//@ ensures pred<int>(nil);
{
	fun_t_arg(123);
}

void call_function_that_accepts_fun_t()
//@ requires pred<int>(nil);
//@ ensures pred<int>(nil);
{
	//@ produce_function_pointer_chunk fun_t<int>(fun)(fun2)(i) { call(); }
	accept_fun_t_int(fun);
}
