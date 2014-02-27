#include <stdio.h>
#include <stdlib.h>
#include <stddef.h>
#include <string.h>

#define CARD_NUMBER_SIZE 8
#define CARD_NUMBER_MASKED_SIZE 4

/*@

// From rF* example:
//   val last_four : n:hi int -> s:string {|(L n = R n) % 10000 => L s = R s|}
//   let last_four n = "********" ^ int2string (n%10000)

lemma void INFORMATION_FLOW(list<char> first, list<char> second, int masked_numbers)
  requires length(first) == length(second) &*& 0 <= masked_numbers &*& masked_numbers < length(second);
  ensures  drop(masked_numbers, first) == drop(masked_numbers, second) ?
             ghost_mask_card_number(first, masked_numbers) == 
             ghost_mask_card_number(second, masked_numbers) : true;
{
  switch (first)
  {
    case nil :
      switch (second)
      { 
        case nil : first == second;
        case cons(x, xs) : assert false;
      }
    case cons(x, xs) :
      switch (second)
      { 
        case nil : assert false;
        case cons(x0, xs0) :
          if (masked_numbers == 0) 
          {}
          else
          {
            INFORMATION_FLOW(xs, xs0, masked_numbers - 1);
          }
      }
  }
}
@*/

/*@
fixpoint list<char> ghost_mask_card_number(list<char> number, size_t n)
{
    switch(number)
    {
        case nil: return nil;
        case cons(x, xs): return 
          n == 0 ? number : 
                   cons('*', ghost_mask_card_number(xs, n - 1));
    }
}

lemma void test_mask_empty(list<char> number)
  requires true;
  ensures  ghost_mask_card_number(number, 0) == number;
{
  switch (number)
  {
    case nil:
    case cons(x, xs):
  }
}
@*/

void mask_card_number_core(char* masked_number, char* number, int masked, int size)
  /*@ requires 0 <= masked &*& masked <= size &*&
               [?f]chars(number, size, ?n_digits) &*&
               chars(masked_number, size, _);
  @*/
  /*@ ensures  [f]chars(number, size, n_digits) &*&
               chars(masked_number, size, ?r_digits) &*&
               r_digits == ghost_mask_card_number(n_digits, masked); 
  @*/
{
  if (masked == 0)
  {
    memcpy(masked_number, number, (size_t) size);
    
    //@ assert (masked == 0);
    //@ assert chars(masked_number, size, ?temp);
    //@ test_mask_empty(temp); 
  }
  else
  {
    //@ chars_limits(masked_number);
    //@ chars_limits(number);
    mask_card_number_core(masked_number + 1, number + 1, masked - 1, size - 1);
    masked_number[0] = '*';
  }
}

char* mask_card_number(char* number)
  /*@ requires [?f]chars(number, CARD_NUMBER_SIZE + 1, ?n_digits); @*/
  /*@ ensures  [f]chars(number, CARD_NUMBER_SIZE + 1, n_digits) &*&
               malloc_block_chars(result, CARD_NUMBER_SIZE + 1) &*&
               chars(result, CARD_NUMBER_SIZE + 1, ?r_digits) &*&
               r_digits == ghost_mask_card_number(n_digits, CARD_NUMBER_MASKED_SIZE); 
  @*/
{
  char *result = malloc((CARD_NUMBER_SIZE + 1) * sizeof(char));
  if (result == 0){abort();}
  
  mask_card_number_core(result, number, CARD_NUMBER_MASKED_SIZE, CARD_NUMBER_SIZE + 1);
  
  return result;
}

int main() //@ : main
  //@ requires true;
  //@ ensures true;
{
  printf("Non interferance:\n");
  
  char* number;
  char* masked_number;
  
  number = "01234567";
  //@ string_to_chars(number);
  masked_number = mask_card_number(number);
  //@ assert chars(masked_number, 9, {'*', '*', '*', '*', '4', '5', '6', '7', 0});
  //@ chars_to_string(number);
  printf("\tcard nb: %s -> %s\n", number, masked_number);
  free(masked_number);
  
  number = "11111111";
  //@ string_to_chars(number);
  masked_number = mask_card_number(number);
  //@ assert chars(masked_number, 9, {'*', '*', '*', '*', '1', '1', '1', '1', 0});
  //@ chars_to_string(number);
  printf("\tcard nb: %s -> %s\n", number, masked_number);
  free(masked_number);
  
  number = "22221111";
  //@ string_to_chars(number);
  masked_number = mask_card_number(number);
  //@ assert chars(masked_number, 9, {'*', '*', '*', '*', '1', '1', '1', '1', 0});
  //@ chars_to_string(number);
  printf("\tcard nb: %s -> %s\n", number, masked_number);  
  free(masked_number);

  return 0;
}

