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

void write_identifier(char *arr, int id);
  /*@ requires [_]public_invar(?pub) &*&
               chars(arr, ID_SIZE, _); @*/
  /*@ ensures  crypto_chars(normal, arr, ID_SIZE, identifier(id)) &*&
               [_]public_generated(pub)(identifier(id)); @*/

/*@
predicate check_identifier_ghost_args(bool sym, bool garbage, int p_key,
                                      int c_key, list<char> cs_rest) = true;
@*/

void check_identifier(char *arr, int id);
  /*@ requires [_]public_invar(?pub) &*&
               [_]decryption_key_classifier(?key_classifier) &*&
               network_permission(?p) &*&
               [?f]crypto_chars(normal, arr, ID_SIZE, ?cs) &*&
               check_identifier_ghost_args(?sym, ?garbage, ?p_key,
                                           ?c_key, ?cs_rest) &*&
               garbage ?
                 decryption_garbage(sym, p, ?s, p_key, c_key,
                                    append(cs, cs_rest)) &*&
                 s == known_value(0, identifier(id))
               :
                 true; @*/
  /*@ ensures  network_permission(p) &*&
               [f]crypto_chars(normal, arr, ID_SIZE, cs) &*&
               cs == identifier(id) &*&
               garbage ?
                 decryption_permission(p) &*&
                 key_classifier(p_key, c_key, sym) ? true : col
               :
                 true; @*/

#endif
