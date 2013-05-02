
// Test containing bad code to check whether VeriFast catches it.

/*@
predicate pred<a>(list<a> l);
@*/

typedef void fun_t/*@<a> @*/();
//@ requires pred<a>(?l);
//@ ensures pred<a>(l);

void fun()
//@ : fun_t<int> 
//@ requires pred<char>(?l); //~ should-fail
//@ ensures pred<char>(l);
{
}
