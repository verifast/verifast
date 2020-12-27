
/*@
predicate pred<a>(list<a> l);
@*/

typedef void fun_t/*@<a, b> @*/();
//@ requires pred<a>(?l);
//@ ensures pred<a>(l);

void fun()
//@ : fun_t<int, int>()
//@ requires pred<int>(?l);
//@ ensures pred<int>(l);
{
}

void accept_fun_t_int(fun_t *fun_t_arg)
//@ requires [_]is_fun_t<int>(fun_t_arg) &*& pred<int>(nil); //~ should-fail
//@ ensures pred<int>(nil);
{
	//fun_t_arg();
}
