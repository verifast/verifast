
/*@
predicate pred<a>(list<a> l);
@*/

typedef void fun_t/*@<a> @*/();
//@ requires pred<a>(?l);
//@ ensures pred<a>(l);

void fun()
//@ : fun_t<int>()
//@ requires pred<int>(?l);
//@ ensures pred<int>(l);
{
}

void accept_fun_t_int(fun_t *fun_t_arg)
//@ requires [_]is_fun_t<int>(fun_t_arg) &*& pred<int>(nil);
//@ ensures pred<int>(nil);
{
	fun_t_arg();
}

void call_function_that_accepts_fun_t()
//@ requires pred<int>(nil);
//@ ensures pred<int>(nil);
{
	/*@
	produce_function_pointer_chunk fun_t<int, int>(fun)()() { //~ should-fail
		//call();
	}
	@*/
	//accept_fun_t_int(fun);
}
