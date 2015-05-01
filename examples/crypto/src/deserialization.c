#include "deserialization.h"

#include "principals.h"
//@ #include "list.gh"
#include "serialization.h"

/*@

#define DESERIALIZE_ITEM_PROOF_1(CS, SIZE) \
  open [_]polarssl_public_generated_chars(polarssl_pub(pub))(CS); \
  polarssl_public_generated_chars_split(polarssl_pub(pub), CS, SIZE); \
  polarssl_cryptograms_in_chars_bound_to(CS); \
  polarssl_cryptograms_in_chars_bound_split( \
                                   CS, polarssl_cryptograms_in_chars(CS), SIZE);

#define DESERIALIZE_ITEM_PROOF_2(TAG, CG) \
  polarssl_cryptogram cg = \
                         polarssl_chars_for_cryptogram_surjective(cs_cg, TAG); \
  list<polarssl_cryptogram> cgs = polarssl_cryptograms_in_chars(cs_cg); \
  assert cg == CG; \
  polarssl_public_generated_chars_extract(polarssl_pub(pub), cs_cg, cg); \
  polarssl_cryptograms_in_chars_bound_to(cs_cg); \
  polarssl_cryptogram_in_bound(cs_cg, cg, cgs); \
  polarssl_cryptograms_in_chars_bound_from(cs_cg, \
                                           polarssl_cryptograms_in_chars(cs)); \
  mem_subset(cg, cgs, polarssl_cryptograms_in_chars(cs)); \
  
#define DESERIALIZE_ITEM_PROOF_3(I1, I2, PROOF) \
  open [_]polarssl_pub(pub)(cg); \
  assert [_]exists(?col); \
  item i; \
  if (col) \
  { \
    if (well_formed(cs_pay0, nat_length(cs_pay0))) \
    { \
      switch(level_bound) \
      { \
        case succ(level_bound0): \
          close proof_obligations(pub); \
          DESERIALIZE_ITEM_PROOF_3_1(I1) \
          open proof_obligations(pub); \
          PROOF \
        case zero: \
          DESERIALIZE_ITEM_PROOF_3_2 \
      } \
    } \
    else \
    { \
      DESERIALIZE_ITEM_PROOF_3_3(I2, PROOF) \
    } \
  } \
  else \
  { \
    DESERIALIZE_ITEM_PROOF_3_4(I1) \
  } \
  close item_constraints_no_collision(i, cs, pub); \
  leak item_constraints_no_collision(i, cs, pub); \
  assert [_]pub(i); \
  assert [_]item_constraints_no_collision(i, cs, pub); \

#define DESERIALIZE_ITEM_PROOF_3_1(I) \
  well_formed_upper_bound(cs_pay0, nat_length(cs_pay0), nat_of_int(INT_MAX)); \
  forall_mem(cg, polarssl_cryptograms_in_chars(cs), \
                    (polarssl_cryprogram_has_lower_level)(succ(level_bound))); \
  polarssl_cryptogram_level_nested_constraints_bound(cg, level_bound); \
  deserialize_item_(level_bound0, nat_of_int(INT_MAX), cs_pay0, pub); \
  open [_]item_constraints_no_collision(?pay0, cs_pay0, pub); \
  assert [_]pub(pay0); \
  i = I; \
  close well_formed_item_chars(I)(cs_pay0); \
  leak well_formed_item_chars(I)(cs_pay0); \
  
#define DESERIALIZE_ITEM_PROOF_3_2 \
  polarssl_cryptogram_level_flat_constraints(cg); \
  assert polarssl_cryptogram_level(cg) != zero; \
  polarssl_cryptogram_constraints(cs_cg, cg); \
  forall_mem(cg, polarssl_cryptograms_in_chars(cs), \
                    (polarssl_cryprogram_has_lower_level)(succ(level_bound))); \
  assert polarssl_cryptogram_level(cg) == zero; \
  assert false;

#define DESERIALIZE_ITEM_PROOF_3_3(I, PROOF) \
  i = I; \
  PROOF \
  close ill_formed_item_chars(I)(cs_pay0); \
  leak ill_formed_item_chars(I)(cs_pay0); \

#define DESERIALIZE_ITEM_PROOF_3_4(I) \
  assert [_]item_constraints_no_collision(?pay0, cs_pay0, pub); \
  i = I; \
  item_constraints_no_collision_well_formed(pay0, i); \
  assert [_]pub(i); \

#define DESERIALIZE_ITEM_PROOF \
switch(length_bound) \
{ \
  case succ(length_bound0): \
    open proof_obligations(pub); \
    if (head(cs) == 'a') \
    { \
      assert cs == cons('a', ?cs0); \
      item i = data_item(cs0); \
      assert is_public_data(?proof, pub); \
      close exists(polarssl_info_for_item); \
      proof(i); \
      close item_constraints_no_collision(i, cs, pub); \
      leak item_constraints_no_collision(i, cs, pub); \
    } \
    else if (head(cs) == 'b') \
    { \
      assert cs == cons('b', ?cs0); \
      DESERIALIZE_ITEM_PROOF_1(cs, 1); \
      \
      int length_f_cs; \
      list<char> p_cs, f_cs, s_cs; \
      \
      if (length(cs) == 1) \
      { \
        assert false; \
      } \
      else if (INT_MIN <= head(tail(cs)) && head(tail(cs)) <= INT_MAX) \
      { \
        length_f_cs = int_of_chars(take(sizeof(int), tail(cs))); \
        p_cs = drop(1 + sizeof(int), cs); \
        f_cs = take(length_f_cs, p_cs); \
        s_cs = drop(length_f_cs, p_cs); \
        \
        list<polarssl_cryptogram> cgs = polarssl_cryptograms_in_chars(cs); \
        list<polarssl_cryptogram> f_cgs = polarssl_cryptograms_in_chars(f_cs); \
        list<polarssl_cryptogram> s_cgs = polarssl_cryptograms_in_chars(s_cs); \
        \
        length_drop(1 + sizeof(int), cs); \
        length_take(length_f_cs, p_cs); \
        length_drop(length_f_cs, p_cs); \
        \
        polarssl_public_generated_chars_split( \
                                         polarssl_pub(pub), cs0, sizeof(int)); \
        polarssl_cryptograms_in_chars_bound_split(cs0, cgs, sizeof(int)); \
        polarssl_public_generated_chars_split( \
                                        polarssl_pub(pub), p_cs, length_f_cs); \
        polarssl_cryptograms_in_chars_bound_split(p_cs, cgs, length_f_cs); \
        \
        open [_]polarssl_public_generated_chars(polarssl_pub(pub))(f_cs); \
        open [_]polarssl_public_generated_chars(polarssl_pub(pub))(s_cs); \
        \
        polarssl_cryptograms_in_chars_bound_from(f_cs, cgs); \
        forall_subset(f_cgs, cgs, polarssl_cryptogram_is_generated); \
        polarssl_cryptograms_in_chars_bound_from(s_cs, cgs); \
        forall_subset(s_cgs, cgs, polarssl_cryptogram_is_generated); \
        \
        forall_subset(f_cgs, cgs, (polarssl_cryprogram_has_lower_level) \
                                  (succ(level_bound))); \
        forall_subset(s_cgs, cgs, (polarssl_cryprogram_has_lower_level) \
                                  (succ(level_bound))); \
      } \
      else \
      { \
        assert false; \
      } \
      close proof_obligations(pub); \
      \
      deserialize_item_(level_bound, length_bound0, f_cs, pub); \
      deserialize_item_(level_bound, length_bound0, s_cs, pub); \
      \
      assert [_]item_constraints_no_collision(?f, f_cs, pub); \
      assert [_]item_constraints_no_collision(?s, s_cs, pub); \
      assert [_]pub(f); \
      assert [_]pub(s); \
      \
      open proof_obligations(pub); \
      assert is_public_pair_compose(?proof, pub); \
      proof(f, s); \
      item i = pair_item(f, s); \
      close item_constraints_no_collision(i, cs, pub); \
      leak item_constraints_no_collision(i, cs, pub); \
    } \
    else if (head(cs) == 'c') \
    { \
      assert cs == cons('c', _); \
      if (length(cs) == 1) \
      { \
        assert false; \
      } \
      else \
      { \
        assert cs == cons('c', cons(?inc, ?cs_cg)); \
        DESERIALIZE_ITEM_PROOF_1(cs, 2) \
        DESERIALIZE_ITEM_PROOF_2(1, polarssl_random(?p0, ?c0)) \
        \
        item i = nonce_item(p0, c0, inc); \
        item i0 = nonce_item(p0, c0, 0); \
        \
        open [_]polarssl_pub(pub)(cg); \
        assert [_]pub(i0); \
        assert is_public_incremented_nonce(?proof, pub); \
        proof(i0, i); \
        \
        close item_constraints_no_collision(i, cs, pub); \
        leak item_constraints_no_collision(i, cs, pub); \
      } \
    } \
    else if (head(cs) == 'd') \
    { \
      assert cs == cons('d', ?cs_cg); \
      DESERIALIZE_ITEM_PROOF_1(cs, 1) \
      DESERIALIZE_ITEM_PROOF_2(5, polarssl_hash(?cs_pay0)) \
      DESERIALIZE_ITEM_PROOF_3(hash_item(some(pay0)), \
                               hash_item(none), \
                               assert is_public_hash(?proof, pub); \
                               proof(i);) \
    } \
    else if (head(cs) == 'e') \
    { \
      assert cs == cons('e', ?cs_cg); \
      DESERIALIZE_ITEM_PROOF_1(cs, 1) \
      DESERIALIZE_ITEM_PROOF_2(2, polarssl_symmetric_key(?p0, ?c0)) \
      \
      open [_]polarssl_pub(pub)(cg); \
      item i = symmetric_key_item(p0, c0); \
      close item_constraints_no_collision(i, cs, pub); \
      leak item_constraints_no_collision(i, cs, pub); \
    } \
    else if (head(cs) == 'f') \
    { \
      assert cs == cons('f', ?cs_cg); \
      DESERIALIZE_ITEM_PROOF_1(cs, 1) \
      DESERIALIZE_ITEM_PROOF_2(3, polarssl_public_key(?p0, ?c0)) \
      \
      open [_]polarssl_pub(pub)(cg); \
      item i = public_key_item(p0, c0); \
      close item_constraints_no_collision(i, cs, pub); \
      leak item_constraints_no_collision(i, cs, pub); \
    } \
    else if (head(cs) == 'g') \
    { \
      assert cs == cons('g', ?cs_cg); \
      DESERIALIZE_ITEM_PROOF_1(cs, 1) \
      DESERIALIZE_ITEM_PROOF_2(4, polarssl_private_key(?p0, ?c0)) \
      \
      open [_]polarssl_pub(pub)(cg); \
      item i = private_key_item(p0, c0); \
      close item_constraints_no_collision(i, cs, pub); \
      leak item_constraints_no_collision(i, cs, pub); \
    } \
    else if (head(cs) == 'h') \
    { \
      assert cs == cons('h', ?cs_cg); \
      DESERIALIZE_ITEM_PROOF_1(cs, 1) \
      DESERIALIZE_ITEM_PROOF_2(6, polarssl_hmac(?p0, ?c0, ?cs_pay0)) \
      DESERIALIZE_ITEM_PROOF_3(hmac_item(p0, c0, some(pay0)), \
                               hmac_item(p0, c0, none), \
                               assert is_public_hmac(?proof, pub); \
                               proof(i);) \
    } \
    else if (head(cs) == 'i') \
    { \
      assert cs == cons('i', ?cs0); \
      assert length(cs) <= INT_MAX; \
      list<char> ent1 = take(GCM_ENT_SIZE, cs0); \
      list<char> cs_cg = drop(GCM_ENT_SIZE, cs0); \
      take_append(GCM_ENT_SIZE, ent1, cs_cg); \
      drop_append(GCM_ENT_SIZE, ent1, cs_cg); \
      \
      open [_]polarssl_public_generated_chars(polarssl_pub(pub))(cs); \
      polarssl_public_generated_chars_split(polarssl_pub(pub), cs, 1); \
      polarssl_cryptograms_in_chars_bound_to(cs); \
      polarssl_cryptograms_in_chars_bound_split( \
                                    cs, polarssl_cryptograms_in_chars(cs), 1); \
      \
      open [_]polarssl_public_generated_chars(polarssl_pub(pub))(cs0); \
      polarssl_public_generated_chars_split(polarssl_pub(pub), \
                                            cs0, GCM_ENT_SIZE); \
      polarssl_cryptograms_in_chars_bound_to(cs0); \
      polarssl_cryptograms_in_chars_bound_split( \
                        cs0, polarssl_cryptograms_in_chars(cs), GCM_ENT_SIZE); \
      \
      polarssl_cryptogram cg = \
                         polarssl_chars_for_cryptogram_surjective(cs_cg, 8); \
      assert cg == polarssl_auth_encrypted(?p0, ?c0, ?mac0, ?cs_pay0, ?iv0); \
      list<char> ent2 = cons(length(mac0), append(mac0, iv0)); \
      take_append(length(mac0), mac0, iv0); \
      drop_append(length(mac0), mac0, iv0); \
      list<char> ent3 = append(ent1, ent2); \
      take_append(GCM_ENT_SIZE, ent1, ent2); \
      drop_append(GCM_ENT_SIZE, ent1, ent2); \
      \
      list<polarssl_cryptogram> cgs = polarssl_cryptograms_in_chars(cs_cg); \
      polarssl_public_generated_chars_extract(polarssl_pub(pub), cs_cg, cg); \
      polarssl_cryptograms_in_chars_bound_to(cs_cg); \
      polarssl_cryptogram_in_bound(cs_cg, cg, cgs); \
      polarssl_cryptograms_in_chars_bound_from(cs_cg, \
                                           polarssl_cryptograms_in_chars(cs)); \
      mem_subset(cg, cgs, polarssl_cryptograms_in_chars(cs)); \
      \
      open [_]polarssl_pub(pub)(cg); \
      assert [_]exists<bool>(?col); \
      item i; \
      if (col) \
      { \
        if (well_formed(cs_pay0, nat_length(cs_pay0))) \
        { \
          switch(level_bound) \
          { \
            case succ(level_bound0): \
              close proof_obligations(pub); \
              well_formed_upper_bound(cs_pay0, nat_length(cs_pay0), \
                                               nat_of_int(INT_MAX)); \
              \
              forall_mem(cg, polarssl_cryptograms_in_chars(cs), \
                         (polarssl_cryprogram_has_lower_level)(succ(level_bound))); \
              assert true == (polarssl_cryprogram_has_lower_level(succ(level_bound), cg)); \
              polarssl_cryptogram_level_nested_constraints_bound(cg, level_bound); \
              \
              deserialize_item_(level_bound0, nat_of_int(INT_MAX), \
                                cs_pay0, pub); \
              assert [_]item_constraints_no_collision(?pay0, cs_pay0, pub); \
              open proof_obligations(pub); \
              assert [_]pub(pay0); \
              i = symmetric_encrypted_item(p0, c0, some(pay0), ent3); \
              close well_formed_item_chars(i)(cs_pay0); \
              leak well_formed_item_chars(i)(cs_pay0); \
              assert is_public_symmetric_encrypted(?proof, pub); \
              proof(i); \
            case zero: \
              DESERIALIZE_ITEM_PROOF_3_2 \
          } \
        } \
        else \
        { \
          DESERIALIZE_ITEM_PROOF_3_3(symmetric_encrypted_item(p0, c0, none, ent3), \
                                     assert is_public_symmetric_encrypted(?proof, pub); \
                                     proof(i);) \
        } \
      } \
      else \
      { \
        assert [_]item_constraints_no_collision(?pay0, cs_pay0, pub); \
        assert [_]exists<list<char> >(?ent); \
        item i_orig = symmetric_encrypted_item(p0, c0, some(pay0), ent); \
        assert [_]pub(i_orig); \
        assert is_public_symmetric_encrypted_entropy(?proof, pub); \
        i = symmetric_encrypted_item(p0, c0, some(pay0), ent3); \
        proof(i_orig, ent3); \
        assert [_]pub(i); \
        item_constraints_no_collision_well_formed(pay0, i); \
      } \
      assert [_]pub(i); \
      close symmetric_encryption_entropy(i)(mac0, iv0); \
      leak symmetric_encryption_entropy(i)(mac0, iv0); \
      close item_constraints_no_collision(i, cs, pub); \
      leak item_constraints_no_collision(i, cs, pub); \
    } \
    else if (head(cs) == 'j') \
    { \
      assert cs == cons('j', ?cs_cg); \
      DESERIALIZE_ITEM_PROOF_1(cs, 1) \
      DESERIALIZE_ITEM_PROOF_2(9, polarssl_asym_encrypted(?p0, ?c0, ?cs_pay0, ?ent0)) \
      DESERIALIZE_ITEM_PROOF_3(asymmetric_encrypted_item(p0, c0, some(pay0), ent0), \
                               asymmetric_encrypted_item(p0, c0, none, ent0), \
                               assert is_public_asymmetric_encrypted(?proof, pub); \
                               proof(i);) \
    } \
    else if (head(cs) == 'k') \
    { \
      assert cs == cons('k', ?cs_cg); \
      DESERIALIZE_ITEM_PROOF_1(cs, 1) \
      DESERIALIZE_ITEM_PROOF_2(10, polarssl_asym_signature(?p0, ?c0, ?cs_pay0, ?ent0)) \
      DESERIALIZE_ITEM_PROOF_3(asymmetric_signature_item(p0, c0, some(pay0), ent0), \
                               asymmetric_signature_item(p0, c0, none, ent0), \
                               assert is_public_asymmetric_signature(?proof, pub); \
                               proof(i);) \
    } \
    else \
    { \
      assert false; \
    } \
    close proof_obligations(pub); \
  case zero: \
    assert false; \
}

lemma void deserialize_item_(nat level_bound, nat length_bound,
                             list<char> cs, predicate(item) pub)
  requires collision_in_run() == false &*&
           proof_obligations(pub) &*&
           //knowledge about first inductive paramter
           true == forall(polarssl_cryptograms_in_chars(cs), 
                                           (polarssl_cryprogram_has_lower_level)
                                           (succ(level_bound))) &*&
           //knowledge about second inductive paramter
           length(cs) <= int_of_nat(length_bound) &*&
           true == well_formed(cs, length_bound) &*&
           [_]polarssl_public_generated_chars(polarssl_pub(pub))(cs);
  ensures  proof_obligations(pub) &*&
           [_]item_constraints_no_collision(?i, cs, pub) &*& [_]pub(i);
{
  // Dummy switch to enforce lexicographic induction
  switch(level_bound)
  {
    case succ(l0):
      DESERIALIZE_ITEM_PROOF
    case zero:
      DESERIALIZE_ITEM_PROOF
  }
}

lemma void deserialize_item(list<char> cs, predicate(item) pub)
  requires collision_in_run() == false &*&
           proof_obligations(pub) &*&
           length(cs) <= INT_MAX &*&
           true == well_formed(cs, nat_length(cs)) &*&
           [_]polarssl_public_generated_chars(polarssl_pub(pub))(cs);
  ensures  proof_obligations(pub) &*&
           [_]item_constraints_no_collision(?i, cs, pub) &*& [_]pub(i);
{
  well_formed_upper_bound(cs, nat_length(cs), nat_of_int(INT_MAX));
  open [_]polarssl_public_generated_chars(polarssl_pub(pub))(cs);
  polarssl_cryptograms_generated_level_bound(polarssl_cryptograms_in_chars(cs));
  deserialize_item_(polarssl_cryprogram_level_bound(), 
                    nat_of_int(INT_MAX), cs, pub);
}

@*/

void parse_pair_item(char* message, int size)
  /*@ requires [?f]chars(message, size, ?cs) &*& size > 1 &*&
               cs == cons('b', ?cs0); @*/
  /*@ ensures  [f]chars(message, size, cs) &*&
               true == well_formed(cs, nat_length(cs)); @*/
{
  if (size <= 1 + (int) sizeof(int))
    abort_crypto_lib("Incorrect size for pair item");
  //@ chars_limits(message);
  //@ chars_split(message, 1);
  //@ open [f]chars(message + 1, size - 1, cs0);
  //@ character_limits(message + 1);
  //@ close [f]chars(message + 1, size - 1, cs0);
  //@ chars_limits(message + 1);
  //@ chars_split(message + 1, sizeof(int));
  //@ assert [f]chars(message + 1, sizeof(int), ?size_f_cs);
  //@ assert [f]chars(message + 1 + sizeof(int), size - 1 - sizeof(int), ?cs2);
  //@ chars_to_integer(message + 1);
  int size_f = *((int*) ((void*) message + 1));
  //@ assert size_f == int_of_chars(size_f_cs);
  //@ integer_to_chars(message + 1);
  if (size_f < 0 ||
      size_f > size - 1 - (int) sizeof(int))
    abort_crypto_lib("Incorrect size for pair item");
  int size_s = size - 1 - (int) sizeof(int) - size_f;
  
  //@ chars_limits(message + 1 + sizeof(int));
  //@ chars_split(message + 1 + sizeof(int), size_f);
  char *buffer_f = malloc_wrapper(size_f);
  memcpy(buffer_f, message + 1 + (int) sizeof(int), (unsigned int) size_f);
  //@ assert chars(buffer_f, size_f, ?cs_f);
  char *buffer_s = malloc_wrapper(size_s);
  memcpy(buffer_s, message + 1 + (int) sizeof(int) + size_f, 
         (unsigned int) size_s);
  //@ assert chars(buffer_s, size_s, ?cs_s);
  if (size_f <= 1 || size_s <= 1)
    abort_crypto_lib("Incorrect size for pair item");
  /*@ assert cs0 == append(chars_of_unbounded_int(length(cs_f)), 
                           append(cs_f, cs_s)); @*/
  parse_item(buffer_f, size_f);
  parse_item(buffer_s, size_s);
  //@ chars_join(message + 1 + sizeof(int));
  //@ chars_join(message + 1);
  //@ chars_join(message);
  
  /*@ switch(nat_length(cs))
      {
        case succ(n):
          length_equals_nat_length(cs0);
          well_formed_upper_bound(cs_f, nat_length(cs_f), nat_length(cs0));
          well_formed_upper_bound(cs_s, nat_length(cs_s), nat_length(cs0));
          assert length(cs) > 0;
          assert length(cs) <= INT_MAX;
          assert cs == cons('b', cs0);
          assert true == well_formed(cs_f, nat_length(cs_f));
          assert true == well_formed(cs_s, nat_length(cs_s));
          assert cs0 == append(chars_of_unbounded_int(length(cs_f)), 
                        append(cs_f, cs_s));
          well_formed_pair_item(cs, cs_f, cs_s);
        case zero:
          assert false;
      }
  @*/
  
  free(buffer_f);
  free(buffer_s);
}

void parse_item(char* message, int size)
  /*@ requires [?f]chars(message, size, ?cs) &*& size > 1; @*/
  /*@ ensures  [f]chars(message, size, cs) &*&
               true == well_formed(cs, nat_length(cs)); @*/
{          
  //@ open [f]chars(message, size, cs);
  char tag = *(message);
  //@ close [f]chars(message, size, cs);
  switch (tag)
  {
    case 'a':
      //@ assert true == well_formed(cs, nat_length(cs));
      break;
    case 'b':
      parse_pair_item(message, size);
      break;
    case 'c':
      if (size != 1 + 1 + NONCE_SIZE)
        abort_crypto_lib("Could not parse nonce: illegal size");
      //@ assert true == well_formed(cs, nat_length(cs));
      break;
    case 'd':
      if (size != 1 + HASH_SIZE)
        abort_crypto_lib("Could not parse hash: illegal size");
      //@ assert true == well_formed(cs, nat_length(cs));
      break;
    case 'e':
      if (size != 1 + GCM_KEY_SIZE)
        abort_crypto_lib("Could not parse symmetric key: illegal size");
      //@ assert true == well_formed(cs, nat_length(cs));
      break;
    case 'f':
      //@ assert true == well_formed(cs, nat_length(cs));
      break;
    case 'g':
      //@ assert true == well_formed(cs, nat_length(cs));
      break;
    case 'h':
      //@ assert true == well_formed(cs, nat_length(cs));
      break;
    case 'i':
      if (size <= 1 + GCM_ENT_SIZE)
        abort_crypto_lib("Could not symmetric encrypted item: illegal size");
      //@ assert true == well_formed(cs, nat_length(cs));
      break;
    case 'j':
      if (size <= 1 || size > 1 + RSA_BIT_KEY_SIZE)
        abort_crypto_lib("Could not asymmetric encrypted item: illegal size");
      //@ assert true == well_formed(cs, nat_length(cs));
      break;
    case 'k':
      if (size <= 1 || size > 1 + RSA_BIT_KEY_SIZE)
        abort_crypto_lib("Could not asymmetric signature item: illegal size");
      //@ assert true == well_formed(cs, nat_length(cs));
      break;
    default: 
      abort_crypto_lib("Found illegal tag during deserialization");
  }
}

struct item* deserialize_from_public_message(char* buffer, int size)
  /*@ requires [?f0]world(?pub) &*& 
               [?f1]polarssl_public_message(polarssl_pub(pub)) 
                                           (buffer, size, ?cs); @*/
  /*@ ensures  [f0]world(pub) &*& 
               [f1]polarssl_public_message(polarssl_pub(pub)) 
                                          (buffer, size, cs) &*&
               item(result, ?i, pub) &*& [_]pub(i); @*/
{
  if (size <= 1)
    abort_crypto_lib("Found corrupted item during deserialization");
  struct item* item = malloc(sizeof(struct item));
  if (item == 0){abort_crypto_lib("malloc of item failed");}

  //@ open [f0]world(pub);
  //@ close [f0]world(pub);
  /*@ open [f1]polarssl_public_message(polarssl_pub(pub))
                                      (buffer, size, cs); @*/
  item->size = size;
  item->content = malloc_wrapper(item->size);
  //@ assert item->content |-> ?cont;
  memcpy(item->content, buffer, (unsigned int) size);
  parse_item(buffer, size);
  //@ retreive_proof_obligations();
  /*@ if (collision_in_run())
      {
        item i = dummy_item_for_tag(head(cs));
        collision_public(pub, cs);
        well_formed_valid_tag(cs, nat_length(cs));
        tag_for_dummy_item(i, head(cs));
        close item_constraints(true, i, cs, pub);
        leak item_constraints(true, i, cs, pub);
        open proof_obligations(pub);
        assert is_public_collision(?proof, pub);
        proof(i);
        close proof_obligations(pub);
      }
      else
      {
        deserialize_item(cs, pub);
        assert [_]item_constraints_no_collision(?i, cs, pub);
        close item_constraints(false, i, cs, pub);
        leak item_constraints(false, i, cs, pub);
      }
  @*/
  //@ assert [_]item_constraints(_, ?i, cs, pub);
  //@ leak proof_obligations(pub);

  /*@ close [f1]polarssl_public_message(polarssl_pub(pub))
                                       (buffer, size, cs); @*/
  //@ close item(item, i, pub);
  return item;
}
