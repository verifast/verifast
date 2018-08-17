void memcpy(char *dest, char *src, int count)
//@requires dest[0..count] |-> _ &*& [?f]src[0..count] |-> ?cs;
//@ensures dest[0..count] |-> cs &*& [f]src[0..count] |-> cs; //~ should_fail
{
  for (int i = 0; ; ++i) 
  //@requires dest[i..count] |-> _ &*& [f]src[i..count] |-> ?cs0;
  //@ensures dest[old_i..count] |-> cs0 &*& src[old_i..count] |-> cs0;
  {
    //@ open chars(dest + i, _, _);
    //@ open chars(src + i, _, _);
    if (i == count) break;
    dest[i] = src[i];
  }
}

void test()
//@requires true;
//@ensures true;
{
  char buffer1[7] = "Hello!";
  char buffer2[7];
  memcpy(buffer2, buffer1, 7);
  assert(buffer2[5] == '!');
}
