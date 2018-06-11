#include "identifiers.h"

#include "../stdlib.h"
#include "../string.h"

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
  /*@ ensures  crypto_chars(normal, arr, ID_SIZE, ?ccs) &*&
               ccs == cs_to_ccs(identifier(id)) &*&
               [_]public_ccs(ccs); @*/
{
  void *temp = &id;
  //@ assert integer(temp, ?id_val);
  //@ chars_to_integer(temp);
  //@ assert chars(temp, 4, chars_of_int(id_val));

  //@ chars_limits(arr);
  //@ chars_to_crypto_chars(temp, 4);
  //@ chars_to_crypto_chars(arr, 4);
  //@ chars_to_crypto_chars((void*) arr + 4, 4);
  //@ chars_to_crypto_chars((void*) arr + 8, 4);
  memcpy(arr +  0, temp, 4);
  memcpy(arr +  4, temp, 4);
  memcpy(arr +  8, temp, 4);
  //@ crypto_chars_to_chars(temp, 4);

  //@ crypto_chars_join(arr + 4);
  //@ crypto_chars_join(arr);
  //@ cs_to_ccs_append(chars_of_int(id_val), chars_of_int(id_val));
  /*@ cs_to_ccs_append(chars_of_int(id_val),
                       append(chars_of_int(id_val), chars_of_int(id_val))); @*/
  //@ public_cs(identifier(id_val));
}

void check_identifier(char *arr, int id)
  /*@ requires [_]public_invar(?pub) &*&
               [_]decryption_key_classifier(?key_classifier) &*&
               [?f]crypto_chars(normal, arr, ID_SIZE, ?ccs) &*&
               check_identifier_ghost_args(?sym, ?garbage, ?p, ?p_key,
                                           ?c_key, ?ccs_rest) &*&
               garbage ?
                 decryption_garbage(sym, p, ?s, p_key, c_key,
                                    append(ccs, ccs_rest)) &*&
                 s == known_value(0, cs_to_ccs(identifier(id)))
               :
                 true; @*/
  /*@ ensures  [f]crypto_chars(normal, arr, ID_SIZE, ccs) &*&
               ccs == cs_to_ccs(identifier(id)) &*&
               garbage ?
                 decryption_permission(p) &*&
                 key_classifier(p_key, c_key, sym) ? true : col
               :
                 true; @*/
{
  //@ open check_identifier_ghost_args(sym, garbage, p, p_key, c_key, ccs_rest);
  char temp[ID_SIZE];
  write_identifier(temp, id);
  //@ MEMCMP_PUB(temp)
  //@ MEMCMP_PUB(arr)
  if (memcmp(temp, arr, ID_SIZE) != 0) abort();
  //@ public_crypto_chars(temp, ID_SIZE);
  //@ assert [f]crypto_chars(normal, arr, ID_SIZE, ccs);
  /*@ if (garbage)
      {
        assert decryption_garbage(sym, p, ?s, _, _, _);
        close exists(pair(nil, ccs_rest));
        close has_structure(append(ccs, ccs_rest), s);
        leak has_structure(append(ccs, ccs_rest), s);
        decryption_garbage(arr, ID_SIZE, s);
      }
  @*/
}
