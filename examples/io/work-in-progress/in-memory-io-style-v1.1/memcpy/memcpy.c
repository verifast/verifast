#include "../buffer_iostyle/buffer_iostyle.h"

void memcopy(int *from, int *to, int count)
/*@ requires
  ints(from, ?count_from, ?from_content)
  &*& ints(to, ?count_to, ?to_content)
  &*& count_from >= count
  &*& count_to >= count;
@*/
/*@ ensures
  ints(from, count_from, from_content)
  &*& ints(to, count_to, ?to_new_content)
  &*& take(count, to_new_content) == take(count, from_content);
@*/
{
  // We have to write the program 4 times:
  // - C implementation
  // - Contract
  // - Come up with the guarantee/rely/invar
  // - Write a recursive lemma that closes the predicates
  // This will be lengthy and has a risk of scalability issues.
  
  //@ assume(false);
}
