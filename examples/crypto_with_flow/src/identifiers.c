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
void write_identifier(char *arr, int id)
  /*@ requires [_]public_invar(?pub) &*&
               chars(arr, ID_SIZE, _); @*/
  /*@ ensures  crypto_chars(normal, arr, ID_SIZE, identifier(id)) &*&
               [_]public_generated(pub)(identifier(id)); @*/
{
  void *temp = &id;
  //@ assert integer(temp, ?id_val);
  //@ chars_to_integer(temp);
  //@ assert chars(temp, 4, chars_of_int(id_val));

  //@ chars_limits(arr);
  //@ chars_to_crypto_chars(temp, 4);
  memcpy(arr +  0, temp, 4);
  memcpy(arr +  4, temp, 4);
  memcpy(arr +  8, temp, 4);
  //@ crypto_chars_to_chars(temp, 4);

  //@ crypto_chars_join(arr + 4);
  //@ crypto_chars_join(arr);

  //@ crypto_chars_to_chars(arr, 12);
  //@ public_chars(arr, 12);
}

void check_identifier(char *arr, int id)
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
{
  //@ open check_identifier_ghost_args(sym, garbage, p_key, c_key, cs_rest);
  char temp[ID_SIZE];
  write_identifier(temp, id);
  //@ crypto_chars_to_chars(temp, ID_SIZE);
  //@ public_chars(temp, ID_SIZE);
  //@ chars_to_crypto_chars(temp, ID_SIZE);
  if (memcmp(temp, arr, ID_SIZE) != 0) abort();
  //@ public_crypto_chars(temp, ID_SIZE);
  //@ assert [f]crypto_chars(normal, arr, ID_SIZE, cs);
  /*@ if (garbage)
      {
        assert decryption_garbage(sym, p, ?s, _, _, _);
        close exists(pair(nil, cs_rest));
        close has_structure(append(cs, cs_rest), s);
        leak has_structure(append(cs, cs_rest), s);
        decryption_garbage(arr, ID_SIZE, s);
      }
  @*/
}
