/**
 * If the contract you want to verify against
 * is in the untrusted .c file, you might
 * actually verify against the wrong contract.
 * So there must be a way to say what the contract
 * is, without trusting the .c file refers to the
 * correct contract.
 *
 * This example illustrates how you can set
 * the contract separately. See verify.mysh
 * to see how to invoke VeriFast.
 */

#include <stdio_simple.h>
#include "specification.h"
//#include <stdio.h>

void main() //@ : main_spec
//@ requires token(?t1) &*& example_io(t1, ?t2);
//@ ensures token(t2);
{
  //@ open example_io(_, _);
  putchar('h');
  putchar('i');
}
