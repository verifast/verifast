// Test of line concatenation using backslash.

in\
t ma\
in()
  //@ re\
quires true;
  //@ ensures true;
{
  char *c = "A\
B";
  //@ open [_]chars(c, _);
  char c0 = *c;
  //@ open [_]chars(c + 1, _);
  char c1 = *(c + 1);
  assert(c0 == 'A' && c1 == 'B');
  return 0;
}