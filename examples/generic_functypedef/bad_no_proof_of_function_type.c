
// Test containing bad code to check whether VeriFast catches it.

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
//@ requires pred<int>(nil);
//@ ensures pred<int>(nil);
{
	// no proof that fun_t_arg is of type fun_t<t> for a type t.
	fun_t_arg(); //~ should-fail
}
