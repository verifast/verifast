void error()
//@requires true;
//@ensures true;
{
	while (false) 
	//@invariant true;
	{ int i = 0;}	
	//@ensures true; //~should_fail
	return;
}
