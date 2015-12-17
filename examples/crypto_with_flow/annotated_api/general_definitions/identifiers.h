#ifndef IDENTIFIERS_H
#define IDENTIFIERS_H

//@ #include <crypto.gh>
//@ #include "public_chars.gh"

#define ID_SIZE 12

/*@
 
fixpoint list<char> identifier(int i)
{
  return append(chars_of_int(i), append(chars_of_int(i), chars_of_int(i)));
}

lemma void equal_identifiers(int id1, int id2);
  requires length(chars_of_int(id1)) == 4 &*&
           length(chars_of_int(id2)) == 4 &*&
           identifier(id1) == identifier(id2);
  ensures  id1 == id2;

@*/

void write_identifier(char *array, int id);
  /*@ requires [_]public_invar(?pub) &*&
               chars(array, ID_SIZE, _); @*/
  /*@ ensures  crypto_chars(normal, array, ID_SIZE, identifier(id)) &*&
               [_]public_generated(pub)(identifier(id)); @*/

void check_identifier(char *array, int id);
  /*@ requires [_]public_invar(?pub) &*&
               principal(?p, ?c) &*&
               crypto_chars(?kind, array, ?size, ?cs) &*&
               size >= ID_SIZE; @*/
  /*@ ensures  principal(p, c) &*& kind != garbage || col &*&
               crypto_chars(secret, array, size, cs) &*&
               take(ID_SIZE, cs) == identifier(id) &*&
               [_]public_generated(pub)(take(ID_SIZE, cs)); @*/

#endif