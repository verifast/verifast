
// contains errors to check whether VeriFast finds them.

/*@
predicate pred<a>(list<a> l);
@*/

typedef void fun_t/*@<a> @*/();
//@ requires pred<a>(?l);
//@ ensures pred<a>(l);

void fun()//@ : fun_t<int, char>() //~ should-fail
//@ requires pred<int>(?l);
//@ ensures pred<int>(l);
{
}
