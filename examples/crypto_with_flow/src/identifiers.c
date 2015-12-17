#include "../annotated_api/general_definitions/identifiers.h"

//@ #include <crypto.gh>
#include <string.h>
#include <stdlib.h>

/*@

lemma void equal_identifiers(int id1, int id2)
  requires length(chars_of_int(id1)) == 4 &*&
           length(chars_of_int(id2)) == 4 &*&
           identifier(id1) == identifier(id2);
  ensures  id1 == id2;
{
  list<char> id1_rest = append(chars_of_int(id1), chars_of_int(id1));
  list<char> id2_rest = append(chars_of_int(id2), chars_of_int(id2));
  take_append(4, chars_of_int(id1), id1_rest);
  take_append(4, chars_of_int(id2), id2_rest);
  chars_of_int_injective(id1, id2);
}

@*/
void write_identifier(char *array, int id)
  /*@ requires [_]public_invar(?pub) &*&
               chars(array, ID_SIZE, _); @*/
  /*@ ensures  crypto_chars(normal, array, ID_SIZE, identifier(id)) &*&
               [_]public_generated(pub)(identifier(id)); @*/
{
  void *temp = &id;
  //@ assert integer(temp, ?id_val);
  //@ chars_to_integer(temp);
  //@ assert chars(temp, 4, chars_of_int(id_val));
  
  //@ chars_limits(array);
  //@ chars_to_crypto_chars(temp, 4);
  memcpy(array +  0, temp, 4);
  memcpy(array +  4, temp, 4);
  memcpy(array +  8, temp, 4);
  //@ crypto_chars_to_chars(temp, 4);
  
  //@ crypto_chars_join(array + 4);
  //@ crypto_chars_join(array);
  
  //@ crypto_chars_to_chars(array, 12);
  //@ public_chars(array, 12);
}

void check_identifier(char *array, int id)
  /*@ requires [_]public_invar(?pub) &*&
               principal(?p, ?c) &*&
               crypto_chars(?kind, array, ?size, ?cs) &*&
               size >= ID_SIZE; @*/
  /*@ ensures  principal(p, c) &*& kind != garbage || col &*&
               crypto_chars(secret, array, size, cs) &*&
               take(ID_SIZE, cs) == identifier(id) &*&
               [_]public_generated(pub)(take(ID_SIZE, cs)); @*/
{
  char temp[ID_SIZE];
  write_identifier(temp, id);
  //@ crypto_chars_to_chars(temp, ID_SIZE);
  //@ public_chars(temp, ID_SIZE);
  //@ chars_to_crypto_chars(temp, ID_SIZE);
  if (memcmp(temp, array, ID_SIZE) != 0) abort();
  //@ public_crypto_chars(temp, ID_SIZE);
  //@ assert crypto_chars(?new_kind, array, size, cs);
  //@ if (size == ID_SIZE) assert new_kind == normal;
  /*@ if (col || new_kind == normal) 
      {
        crypto_chars_to_chars(array, size);
        chars_to_secret_crypto_chars(array, size);
      }
  @*/
}