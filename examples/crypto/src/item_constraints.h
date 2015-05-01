#ifndef ITEM_CONSTRAINTS_H
#define ITEM_CONSTRAINTS_H

#include "item.h"
#include "invariants.h"

/*@

fixpoint bool valid_tag(char tag)
{
  return tag == 'a' || tag == 'b' || tag == 'c' ||
         tag == 'd' || tag == 'e' || tag == 'f' || 
         tag == 'g' || tag == 'h' || tag == 'i' || 
         tag == 'j' || tag == 'k';
}

fixpoint bool well_formed(list<char> cs, nat upper_bound)
{
  switch(upper_bound)
  {
    case succ(n):
      return
        //correct length
        length(cs) > 0 && length(cs) <= INT_MAX && 
        //correct tag
        valid_tag(head(cs)) &&
        //correct pair_item
        (
          head(cs) != 'b' ||
          (
            length(cs) > 2 &&
            (
              INT_MIN <= head(tail(cs)) && head(tail(cs)) <= INT_MAX ?
              (
                int_of_chars(take(sizeof(int), tail(cs))) > 0 &&
                length(cs) > 1 + sizeof(int) + 
                            int_of_chars(take(sizeof(int), tail(cs))) &&
                well_formed(take(int_of_chars(take(sizeof(int), tail(cs))),
                                 drop(1 + sizeof(int), cs)), n) &&
                well_formed(drop(int_of_chars(take(sizeof(int), tail(cs))),
                                 drop(1 + sizeof(int), cs)), n)
              )
              :
              (
                head(tail(cs)) > 0 &&
                length(cs) > 2 + head(tail(cs)) &&
                well_formed(take(head(tail(cs)), drop(2, cs)), n) &&
                well_formed(drop(head(tail(cs)), drop(2, cs)), n)
              )
            )
          )
        ) &&
        //correct nonce_item
        (
          head(cs) != 'c' || length(cs) == 1 + 1 + NONCE_SIZE
        ) &&
        //correct hash_item
        (
          head(cs) != 'd' || length(cs) == 1 + HASH_SIZE
        ) &&
        //correct symmetric_key_item
        (
          head(cs) != 'e' || length(cs) == 1 + GCM_KEY_SIZE
        ) &&
        //correct symmetric_encrypted_item
        (
          head(cs) != 'i' || 
          length(cs) >= 1 + GCM_ENT_SIZE
        ) &&
        //correct asymmetric_encrypted_item
        (
          head(cs) != 'j' || 
          length(cs) > 1 && length(cs) <= 1 + RSA_SERIALIZED_KEY_SIZE
        ) &&
        //correct asymmetric_signed_item
        (
          head(cs) != 'k' || 
          length(cs) > 1 && length(cs) <= 1 + RSA_SERIALIZED_KEY_SIZE
        );
    case zero:
      return false;
  }
}

lemma void well_formed_upper_bound(list<char> cs, nat upper_bound1, 
                                                  nat upper_bound2);
  requires true == well_formed(cs, upper_bound1) &*&
           length(cs) <= int_of_nat(upper_bound2);
  ensures  true == well_formed(cs, upper_bound2);

lemma void well_formed_pair_item(list<char> cs, 
                                 list<char> cs_f, list<char> cs_s);
  requires length(cs) > 0 &*& length(cs) <= INT_MAX &*&
           cs == cons('b', ?cs0) &*&
           cs0 == append(chars_of_unbounded_int(length(cs_f)), 
                        append(cs_f, cs_s)) &*&
           well_formed(cs_f, nat_length(cs_f)) &&
           well_formed(cs_s, nat_length(cs_s));
  ensures  true == well_formed(cs, nat_length(cs));

predicate_ctor well_formed_item_chars(item i)(list<char> cs) =
  true == well_formed(cs, nat_length(cs))
;

predicate_ctor ill_formed_item_chars(item i)(list<char> cs) =
  false == well_formed(cs, nat_length(cs))
;

fixpoint int tag_for_item(item i)
{
  switch(i)
  {
    case data_item(cs0):
      return 'a';
    case pair_item(f0, s0):
      return 'b';
    case nonce_item(p0, c0, inc0):
      return 'c';
    case hash_item(pay0):
      return 'd';
    case symmetric_key_item(p0, c0):
      return 'e';
    case public_key_item(p0, c0):
      return 'f';
    case private_key_item(p0, c0):
      return 'g';
    case hmac_item(p0, c0, pay0):
      return 'h';
    case  symmetric_encrypted_item(p0, c0, pay0, ent0):
      return 'i';
    case  asymmetric_encrypted_item(p0, c0, pay0, ent0):
      return 'j';
    case  asymmetric_signature_item(p0, c0, pay0, ent0):
      return 'k';
  }
}

fixpoint item dummy_item_for_tag(int i)
{
  return 
    i == 'b' ?
      pair_item(data_item(nil), data_item(nil)) :
    i == 'c' ?
      nonce_item(-1, -1, -1) :
    i == 'd' ?
      hash_item(none) :
    i == 'e' ?
      symmetric_key_item(-1, -1) :
    i == 'f' ?
      public_key_item(-1, -1) :
    i == 'g' ?
      private_key_item(-1, -1) :
    i == 'h' ?
      hmac_item(-1, -1, none) :
    i == 'i' ?
      symmetric_encrypted_item(-1, -1, none, nil) :
    i == 'j' ?
      asymmetric_encrypted_item(-1, -1, none, nil) :
    i == 'k' ?
      asymmetric_signature_item(-1, -1, none, nil)
    :
      data_item(nil);
}

lemma void tag_for_dummy_item(item i, char t);
  requires valid_tag(t) &&
           i == dummy_item_for_tag(t);
  ensures  t == tag_for_item(i);

lemma void well_formed_valid_tag(list<char> cs, nat len);
  requires true == well_formed(cs, len);
  ensures  true == valid_tag(head(cs));

predicate_ctor symmetric_encryption_entropy(item i)(list<char> mac, 
                                                    list<char> iv) = true;

predicate item_constraints_no_collision(item i, list<char> cs, 
                                        predicate(item) pub) =
  length(cs) > 0 &*& length(cs) <= INT_MAX &*&
  switch(i)
  {
    case data_item(cs0):
      return cs == cons(tag_for_item(i), cs0);
    case pair_item(f0, s0): 
      return cs == cons(tag_for_item(i), ?cs0) &*&
             [_]item_constraints_no_collision(f0, ?cs_f0, pub) &*&
             [_]item_constraints_no_collision(s0, ?cs_s0, pub) &*&
             cs0 == append(chars_of_unbounded_int(length(cs_f0)),
                           append(cs_f0, cs_s0));
    case nonce_item(p0, c0, inc0): 
      return cs == cons(tag_for_item(i), cons(inc0, ?cs_cg)) &*&
             length(cs_cg) == NONCE_SIZE &*&
             cs_cg == polarssl_chars_for_cryptogram(polarssl_random(p0, c0)) &*&
             true == polarssl_cryptogram_is_generated(polarssl_random(p0, c0));
             
    case hash_item(pay0): return
      cs == cons(tag_for_item(i), ?cs_cg) &*&
      length(cs_cg) == HASH_SIZE &*&
      switch(pay0)
      {
        //Created through API or guessed by low-level attacker
        case some(pay1):
          return [_]well_formed_item_chars(i)(?cs_pay0) &*&
                 length(cs_pay0) <= INT_MAX &*&
                 [_]item_constraints_no_collision(pay1, cs_pay0, pub) &*&
                 cs_cg == polarssl_chars_for_cryptogram(
                                                     polarssl_hash(cs_pay0)) &*&
                 true == polarssl_cryptogram_is_generated(
                                                        polarssl_hash(cs_pay0));
        //Pulled from network and not well formed
        case none:
          return [_]ill_formed_item_chars(i)(?cs_pay0) &*& 
                 length(cs_pay0) <= INT_MAX &*&
                 [_]polarssl_public_generated_chars(polarssl_pub(pub))
                                                   (cs_pay0) &*&
                 cs_cg == polarssl_chars_for_cryptogram(
                                                     polarssl_hash(cs_pay0)) &*&
                 true == polarssl_cryptogram_is_generated(
                                                        polarssl_hash(cs_pay0));
      };
    case symmetric_key_item(p0, c0):
      return cs == cons(tag_for_item(i), ?cs_cg) &*&
             length(cs_cg) == GCM_KEY_SIZE &*&
             cs_cg == polarssl_chars_for_cryptogram(
                                             polarssl_symmetric_key(p0, c0)) &*&
             true == polarssl_cryptogram_is_generated(
                                             polarssl_symmetric_key(p0, c0));
    case public_key_item(p0, c0):
      return cs == cons(tag_for_item(i), ?cs_cg) &*&
             cs_cg == polarssl_chars_for_cryptogram(
                                                polarssl_public_key(p0, c0)) &*&
             true == polarssl_cryptogram_is_generated(
                                                polarssl_public_key(p0, c0));
    case private_key_item(p0, c0):
      return cs == cons(tag_for_item(i), ?cs_cg) &*&
             cs_cg == polarssl_chars_for_cryptogram(
                                               polarssl_private_key(p0, c0)) &*&
             true == polarssl_cryptogram_is_generated(
                                               polarssl_private_key(p0, c0));
    case hmac_item(p0, c0, pay0): return
      cs == cons(tag_for_item(i), ?cs_cg) &*&
      length(cs) <= INT_MAX &*&
      switch(pay0)
      {
        //Created through API or guessed by low-level attacker
        case some(pay1):
          return [_]well_formed_item_chars(i)(?cs_pay0) &*&
                 length(cs_pay0) <= INT_MAX &*&
                 [_]item_constraints_no_collision(pay1, cs_pay0, pub) &*&
                 cs_cg == polarssl_chars_for_cryptogram(
                                             polarssl_hmac(p0, c0, cs_pay0)) &*&
                 true == polarssl_cryptogram_is_generated(
                                             polarssl_hmac(p0, c0, cs_pay0));
        //Pulled from network and not well formed
        case none:
          return [_]ill_formed_item_chars(i)(?cs_pay0) &*& 
                 length(cs_pay0) <= INT_MAX &*&
                 [_]pub(symmetric_key_item(p0, c0)) &*&
                 [_]polarssl_public_generated_chars(polarssl_pub(pub))
                                                   (cs_pay0) &*&
                 cs_cg == polarssl_chars_for_cryptogram(
                                             polarssl_hmac(p0, c0, cs_pay0)) &*&
                 true == polarssl_cryptogram_is_generated(
                                             polarssl_hmac(p0, c0, cs_pay0));
      };
    case symmetric_encrypted_item(p0, c0, pay0, ent0): return
      cs == cons(tag_for_item(i), ?cs0) &*&
      length(cs) <= INT_MAX &*&
      take(GCM_ENT_SIZE, ent0) == take(GCM_ENT_SIZE, cs0) &*&
      GCM_ENT_SIZE <= length(cs0) &*&
      GCM_ENT_SIZE <= length(ent0) &*&
      [_]symmetric_encryption_entropy(i)(?mac0, ?iv0) &*&
      drop(GCM_ENT_SIZE, ent0) == cons(length(mac0), append(mac0, iv0)) &*&
      switch(pay0)
      {
        //Created through API or guessed by low-level attacker
        case some(pay1):
          return [_]well_formed_item_chars(i)(?cs_pay0) &*&
                 length(cs_pay0) <= INT_MAX &*&
                 [_]item_constraints_no_collision(pay1, cs_pay0, pub) &*&
                 drop(GCM_ENT_SIZE, cs0) == polarssl_chars_for_cryptogram(
                   polarssl_auth_encrypted(p0, c0, mac0, cs_pay0, iv0)) &*&
                 true == polarssl_cryptogram_is_generated(
                   polarssl_auth_encrypted(p0, c0, mac0, cs_pay0, iv0));

        //Pulled from network and not well formed
        case none:
          return [_]ill_formed_item_chars(i)(?cs_pay0) &*& 
                 length(cs_pay0) <= INT_MAX &*&
                 [_]pub(symmetric_key_item(p0, c0)) &*&
                 [_]polarssl_public_generated_chars(polarssl_pub(pub))
                                                   (cs_pay0) &*&
                 drop(GCM_ENT_SIZE, cs0) == polarssl_chars_for_cryptogram(
                   polarssl_auth_encrypted(p0, c0, mac0, cs_pay0, iv0)) &*&
                 true == polarssl_cryptogram_is_generated(
                   polarssl_auth_encrypted(p0, c0, mac0, cs_pay0, iv0));
      };
    case asymmetric_encrypted_item(p0, c0, pay0, ent0): return
      cs == cons(tag_for_item(i), ?cs_cg) &*&
      length(cs_cg) > 0 &*& length(cs_cg) <= RSA_SERIALIZED_KEY_SIZE &*&
      switch(pay0)
      {
        //Created through API or guessed by low-level attacker
        case some(pay1):
          return [_]well_formed_item_chars(i)(?cs_pay0) &*&
                 length(cs_pay0) <= INT_MAX &*&
                 [_]item_constraints_no_collision(pay1, cs_pay0, pub) &*&
                 cs_cg == polarssl_chars_for_cryptogram(
                              polarssl_asym_encrypted(p0, c0, cs_pay0, ent0)) &*&
                 true == polarssl_cryptogram_is_generated(
                              polarssl_asym_encrypted(p0, c0, cs_pay0, ent0));

        //Pulled from network and not well formed
        case none:
          return [_]ill_formed_item_chars(i)(?cs_pay0) &*& 
                 length(cs_pay0) <= INT_MAX &*&
                 [_]pub(public_key_item(p0, c0)) &*&
                 [_]polarssl_public_generated_chars(polarssl_pub(pub))
                                                   (cs_pay0) &*&
                 cs_cg == polarssl_chars_for_cryptogram(
                              polarssl_asym_encrypted(p0, c0, cs_pay0, ent0)) &*&
                 true == polarssl_cryptogram_is_generated(
                              polarssl_asym_encrypted(p0, c0, cs_pay0, ent0));
      };
    case asymmetric_signature_item(p0, c0, pay0, ent0): return
      cs == cons(tag_for_item(i), ?cs_cg) &*&
      length(cs_cg) > 0 &*& length(cs_cg) <= RSA_SERIALIZED_KEY_SIZE &*&
      switch(pay0)
      {
        //Created through API or guessed by low-level attacker
        case some(pay1):
          return [_]well_formed_item_chars(i)(?cs_pay0) &*&
                 length(cs_pay0) <= INT_MAX &*&
                 [_]item_constraints_no_collision(pay1, cs_pay0, pub) &*&
                 cs_cg == polarssl_chars_for_cryptogram(
                              polarssl_asym_signature(p0, c0, cs_pay0, ent0)) &*&
                 true == polarssl_cryptogram_is_generated(
                              polarssl_asym_signature(p0, c0, cs_pay0, ent0));

        //Pulled from network and not well formed
        case none:
          return [_]ill_formed_item_chars(i)(?cs_pay0) &*& 
                 length(cs_pay0) <= INT_MAX &*&
                 [_]pub(private_key_item(p0, c0)) &*&
                 [_]polarssl_public_generated_chars(polarssl_pub(pub))
                                                   (cs_pay0) &*&
                 cs_cg == polarssl_chars_for_cryptogram(
                              polarssl_asym_signature(p0, c0, cs_pay0, ent0)) &*&
                 true == polarssl_cryptogram_is_generated(
                              polarssl_asym_signature(p0, c0, cs_pay0, ent0));
      };
  }
;

lemma void item_constraints_no_collision_well_formed(item i1, item i2);
  requires [_]item_constraints_no_collision(i1, ?cs, ?pub);
  ensures  [_]well_formed_item_chars(i2)(cs);

lemma void item_constraints_no_collision_surjective(list<char> cs1, 
                                                    list<char> cs2, item i);
  requires true == well_formed_item(i) &*&
           [_]item_constraints_no_collision(i, cs1, ?pub) &*&
           [_]item_constraints_no_collision(i, cs2, pub);
  ensures  collision_in_run() ? true : cs1 == cs2;

lemma void item_constraints_no_collision_injective(list<char> cs, item i1,  
                                                                  item i2);
  requires [_]item_constraints_no_collision(i1, cs, ?pub) &*&
           [_]item_constraints_no_collision(i2, cs, pub);
  ensures  collision_in_run() ? true : i1 == i2;

lemma void item_constraints_no_collision_bijective(
                                                 list<char> cs1, list<char> cs2,
                                                 item i1, item i2);
  requires true == well_formed_item(i1) &*&
           [_]item_constraints_no_collision(i1, cs1, ?pub) &*&
           [_]item_constraints_no_collision(i2, cs2, pub);
  ensures  collision_in_run() ? true : true == ((cs1 == cs2) == (i1 == i2));

predicate item_constraints(bool collision, item i, list<char> cs, 
                           predicate(item) pub) =
  true == well_formed(cs, nat_length(cs)) &*&
  collision ?
  (
    [_]polarssl_public_generated_chars(polarssl_pub(pub))(cs) &*&
    collision_in_run() == true &&
    tag_for_item(i) == head(cs)
  )
  :
  [_]item_constraints_no_collision(i, cs, pub)
;

lemma void item_constraints_well_formed(item i1, item i2);
  requires [_]item_constraints(_, i1, ?cs, ?pub);
  ensures  [_]well_formed_item_chars(i2)(cs);

lemma void item_constraints_surjective(list<char> cs1, list<char> cs2, item i);
  requires true == well_formed_item(i) &*&
           [_]item_constraints(_, i, cs1, ?pub) &*&
           [_]item_constraints(_, i, cs2, pub);
  ensures  collision_in_run() ? true : cs1 == cs2;

lemma void item_constraints_injective(list<char> cs, item i1, item i2);
  requires [_]item_constraints(_, i1, cs, ?pub) &*&
           [_]item_constraints(_, i2, cs, pub);
  ensures  collision_in_run() ? true : i1 == i2;

lemma void item_constraints_bijective(list<char> cs1, list<char> cs2,
                                      item i1, item i2);
  requires true == well_formed_item(i1) &*&
           [_]item_constraints(_, i1, cs1, ?pub) &*&
           [_]item_constraints(_, i2, cs2, pub);
  ensures  collision_in_run() ? true : true == ((cs1 == cs2) == (i1 == i2));

@*/

#endif
