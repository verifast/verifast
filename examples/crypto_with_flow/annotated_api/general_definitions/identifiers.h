#ifndef IDENTIFIERS_H
#define IDENTIFIERS_H

//@ #include <crypto.gh>
//@ #include "public_chars.gh"
//@ #include "decryption.gh"

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

/*@
predicate check_identifier_ghost_args(bool sym, bool wrong_key, 
                                      int p_key, int c_key) = true;
@*/
  
void check_identifier(char *array, int id);
  /*@ requires [_]public_invar(?pub) &*&
               [_]decryption_key_classifier(?key_classifier) &*&
               network_permission(?p) &*& 
               [?f]crypto_chars(?kind, array, ?size, ?cs) &*&
               size >= ID_SIZE &*&
               check_identifier_ghost_args(?sym, ?wrong_key, ?p_key, ?c_key) &*&
               wrong_key ?
                 decryption_with_wrong_key(sym, p, ?s, p_key, c_key, cs) &*&
                 s == known_value(0, identifier(id))
               :
                 true; @*/
  /*@ ensures  network_permission(p) &*& 
               [f]crypto_chars(secret, array, size, cs) &*&
               take(ID_SIZE, cs) == identifier(id) &*&
               [_]public_generated(pub)(take(ID_SIZE, cs)) &*&
               wrong_key ?
                 decryption_permission(p) &*& 
                 key_classifier(p_key, c_key, sym) ? true : col
               :
                 true; @*/

#endif