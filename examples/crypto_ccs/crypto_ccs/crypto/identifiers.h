#ifndef IDENTIFIERS_H
#define IDENTIFIERS_H

//@ #include "cryptogram.gh"
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
               chars_(array, ID_SIZE, _); @*/
  /*@ ensures  crypto_chars(normal, array, ID_SIZE, ?ccs) &*&
               ccs == cs_to_ccs(identifier(id)) &*&
               [_]public_ccs(ccs); @*/

/*@
predicate check_identifier_ghost_args(bool sym, bool garbage, int p, int p_key,
                                      int c_key, list<crypto_char> ccs_rest) =
  true;
@*/

void check_identifier(char *array, int id);
  /*@ requires [_]public_invar(?pub) &*&
               [_]decryption_key_classifier(?key_classifier) &*&
               [?f]crypto_chars(normal, array, ID_SIZE, ?ccs) &*&
               check_identifier_ghost_args(?sym, ?garbage, ?p, ?p_key,
                                           ?c_key, ?ccs_rest) &*&
               garbage ?
                 decryption_garbage(sym, p, ?s, p_key, c_key,
                                    append(ccs, ccs_rest)) &*&
                 s == known_value(0, cs_to_ccs(identifier(id)))
               :
                 true; @*/
  /*@ ensures  [f]crypto_chars(normal, array, ID_SIZE, ccs) &*&
               ccs == cs_to_ccs(identifier(id)) &*&
               garbage ?
                 decryption_permission(p) &*&
                 key_classifier(p_key, c_key, sym) ? true : col
               :
                 true; @*/

#endif