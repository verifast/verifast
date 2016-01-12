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
{
  //@ open check_identifier_ghost_args(sym, wrong_key, p_key, c_key);
  char temp[ID_SIZE];
  write_identifier(temp, id);
  //@ crypto_chars_to_chars(temp, ID_SIZE);
  //@ public_chars(temp, ID_SIZE);
  //@ chars_to_crypto_chars(temp, ID_SIZE);
  if (memcmp(temp, array, ID_SIZE) != 0) abort();
  //@ public_crypto_chars(temp, ID_SIZE);
  //@ assert [f]crypto_chars(kind, array, size, cs);
  /*@ if (wrong_key)
      {
        assert decryption_with_wrong_key(sym, p, ?s, p_key, c_key, cs);
        close exists(pair(nil, drop(ID_SIZE, cs)));
        close has_structure(cs, s);
        leak has_structure(cs, s);
        decryption_with_wrong_key(array, size, s);
      }
  @*/
  /*@ switch (kind)
      {
        case normal:
          chars_to_secret_crypto_chars(array, size);
        case secret:
      }
  @*/
}