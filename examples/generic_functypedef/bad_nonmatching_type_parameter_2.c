
// Test containing bad code to check whether VeriFast catches it.

/*@
predicate pred<a>(list<a> l);
@*/

typedef void fun_t/*@<a> @*/();
//@ requires pred<a>(?l);
//@ ensures pred<a>(l);

void fun()
//@ requires pred<char>(?l);
//@ ensures pred<char>(l);
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
	// fun is fun_t<char> but not fun_t<int>
	//@ produce_function_pointer_chunk fun_t<int>(fun)()() { call(); } //~ should_fail
	
}
