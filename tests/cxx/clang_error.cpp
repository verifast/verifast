// Errors reported by Clang are passed on to VeriFast by the AST exporter.

void test()
//@ requires true;
//@ ensures true;
{
  int x = nullptr; //~ should_fail
}
