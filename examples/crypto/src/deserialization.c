#include "deserialization.h"

#include "principals.h"
//@ #include "list.gh"
#include "serialization.h"

/*@

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
      polarssl_cryptograms_in_chars_public_upper_bound_split( \
                                                    polarssl_pub(pub), cs, 1); \
      polarssl_cryptograms_in_chars_split(cs, 1); \
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
        length_drop(1 + sizeof(int), cs); \
        length_take(length_f_cs, p_cs); \
        length_drop(length_f_cs, p_cs); \
        \
        polarssl_cryptograms_in_chars_public_upper_bound_split( \
                                        polarssl_pub(pub), cs0, sizeof(int)); \
        polarssl_cryptograms_in_chars_split(cs0, sizeof(int)); \
        polarssl_cryptograms_in_chars_public_upper_bound_split( \
                                        polarssl_pub(pub), p_cs, length_f_cs); \
        polarssl_cryptograms_in_chars_split(p_cs, length_f_cs); \
        \
        assert cs0 == append(chars_of_int(length_f_cs), append(f_cs, s_cs)); \
        assert true == forall(polarssl_cryptograms_in_chars(cs), \
                    (polarssl_cryprogram_has_lower_level)(succ(level_bound))); \
        \
        subset_trans(polarssl_cryptograms_in_chars(f_cs), \
                      polarssl_cryptograms_in_chars(p_cs), \
                      polarssl_cryptograms_in_chars(cs0)); \
        subset_trans(polarssl_cryptograms_in_chars(f_cs), \
                      polarssl_cryptograms_in_chars(cs0), \
                      polarssl_cryptograms_in_chars(cs)); \
        subset_trans(polarssl_cryptograms_in_chars(s_cs), \
                      polarssl_cryptograms_in_chars(p_cs), \
                      polarssl_cryptograms_in_chars(cs0)); \
        subset_trans(polarssl_cryptograms_in_chars(s_cs), \
                      polarssl_cryptograms_in_chars(cs0), \
                      polarssl_cryptograms_in_chars(cs)); \
        \
        assert true == subset(polarssl_cryptograms_in_chars(f_cs), \
                              polarssl_cryptograms_in_chars(cs)); \
        assert true == subset(polarssl_cryptograms_in_chars(s_cs), \
                              polarssl_cryptograms_in_chars(cs)); \
        \
        forall_subset(polarssl_cryptograms_in_chars(f_cs), \
                      polarssl_cryptograms_in_chars(cs), \
                      (polarssl_cryprogram_has_lower_level) \
                      (succ(level_bound))); \
        forall_subset(polarssl_cryptograms_in_chars(s_cs), \
                      polarssl_cryptograms_in_chars(cs), \
                      (polarssl_cryprogram_has_lower_level) \
                      (succ(level_bound))); \
        \
        assert true == forall(polarssl_cryptograms_in_chars(f_cs), \
                    (polarssl_cryprogram_has_lower_level)(succ(level_bound))); \
        assert true == forall(polarssl_cryptograms_in_chars(s_cs), \
                    (polarssl_cryprogram_has_lower_level)(succ(level_bound))); \
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
        polarssl_cryptogram cg = \
                          polarssl_chars_for_cryptogram_surjective(cs_cg, 1); \
        assert cg == polarssl_random(?p0, ?c0); \
        polarssl_cryptograms_in_chars_public_upper_bound_split( \
                                                    polarssl_pub(pub), cs, 2); \
        polarssl_cryptogram_in_upper_bound(cs_cg, cg, \
                    polarssl_generated_public_cryptograms(polarssl_pub(pub))); \
        polarssl_generated_public_cryptograms_from(polarssl_pub(pub), cg); \
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
      polarssl_cryptogram cg = \
                           polarssl_chars_for_cryptogram_surjective(cs_cg, 5); \
      assert cg == polarssl_hash(?cs_pay0); \
      polarssl_cryptograms_in_chars_public_upper_bound_split( \
                                                    polarssl_pub(pub), cs, 1); \
      polarssl_cryptogram_in_upper_bound(cs_cg, cg, \
                    polarssl_generated_public_cryptograms(polarssl_pub(pub))); \
      polarssl_generated_public_cryptograms_from(polarssl_pub(pub), cg); \
      \
      open [_]polarssl_pub(pub)(cg); \
      assert [_]exists(?col); \
      item i; \
      if (col) \
      { \
        assert true == subset(polarssl_cryptograms_in_chars(cs_pay0), \
                  polarssl_generated_public_cryptograms(polarssl_pub(pub))); \
        polarssl_cryptograms_in_chars_split(cs, 1); \
        if (well_formed(cs_pay0, nat_length(cs_pay0))) \
        { \
          switch(level_bound) \
          { \
            case succ(level_bound0): \
              close proof_obligations(pub); \
              well_formed_upper_bound(cs_pay0, nat_length(cs_pay0), \
                                               nat_of_int(INT_MAX)); \
              polarssl_cryptograms_in_chars_upper_bound_to(cs_pay0, \
                                      polarssl_cryptograms_in_chars(cs_pay0)); \
              polarssl_cryptograms_in_chars_upper_bound_subset( \
                    cs_pay0, polarssl_cryptograms_in_chars(cs_pay0), \
                    polarssl_generated_public_cryptograms(polarssl_pub(pub))); \
              polarssl_cryptogram_constraints(cs_cg, cg); \
              forall_mem(cg, polarssl_cryptograms_in_chars(cs), \
                         (polarssl_cryprogram_has_lower_level) \
                         (succ(level_bound))); \
              polarssl_cryptogram_level_nested_constraints_upper_bound( \
                                                             cg, level_bound); \
              \
              assert true == well_formed(cs_pay0, nat_of_int(INT_MAX)); \
              assert true == forall( \
                   polarssl_cryptograms_in_chars(cs_pay0), \
                   (polarssl_cryprogram_has_lower_level)(succ(level_bound0))); \
              assert length(cs_pay0) <= INT_MAX; \
              assert true == polarssl_cryptograms_in_chars_upper_bound( \
                               cs_pay0, polarssl_generated_public_cryptograms( \
                                                          polarssl_pub(pub))); \
              deserialize_item_(level_bound0, nat_of_int(INT_MAX), \
                                cs_pay0, pub); \
              open [_]item_constraints_no_collision(?pay0, cs_pay0, pub); \
              open proof_obligations(pub); \
              assert [_]pub(pay0); \
              i = hash_item(some(pay0)); \
              close well_formed_item_chars(i)(cs_pay0); \
              leak well_formed_item_chars(i)(cs_pay0); \
              assert is_public_hash(?proof, pub); \
              proof(i); \
              close item_constraints_no_collision(i, cs, pub); \
              leak item_constraints_no_collision(i, cs, pub); \
            case zero: \
              polarssl_cryptogram_level_flat_constraints(cg); \
              assert polarssl_cryptogram_level(cg) != zero; \
              polarssl_cryptogram_constraints(cs_cg, cg); \
              forall_mem(cg, polarssl_cryptograms_in_chars(cs), \
                    (polarssl_cryprogram_has_lower_level)(succ(level_bound))); \
              assert polarssl_cryptogram_level(cg) == zero; \
              assert false; \
          } \
        } \
        else \
        { \
          i = hash_item(none); \
          assert is_public_hash(?proof, pub); \
          proof(i); \
          close ill_formed_item_chars(i)(cs_pay0); \
          leak ill_formed_item_chars(i)(cs_pay0); \
          close item_constraints_no_collision(i, cs, pub); \
          leak item_constraints_no_collision(i, cs, pub); \
        } \
      } \
      else \
      { \
        assert [_]item_constraints_no_collision(?pay0, cs_pay0, pub); \
        i = hash_item(some(pay0)); \
        item_constraints_no_collision_well_formed(pay0, i); \
        assert [_]pub(i); \
        close item_constraints_no_collision(i, cs, pub); \
        leak item_constraints_no_collision(i, cs, pub); \
      } \
      assert [_]pub(i); \
      assert [_]item_constraints_no_collision(i, cs, pub); \
    } \
    else if (head(cs) == 'e') \
    { \
      assert cs == cons('e', ?cs_cg); \
      polarssl_cryptogram cg = \
                          polarssl_chars_for_cryptogram_surjective(cs_cg, 2); \
      assert cg == polarssl_symmetric_key(?p0, ?c0); \
      polarssl_cryptograms_in_chars_public_upper_bound_split( \
                                                    polarssl_pub(pub), cs, 1); \
      polarssl_cryptogram_in_upper_bound(cs_cg, cg, \
                    polarssl_generated_public_cryptograms(polarssl_pub(pub))); \
      polarssl_generated_public_cryptograms_from(polarssl_pub(pub), cg); \
      \
      open [_]polarssl_pub(pub)(cg); \
      item i = symmetric_key_item(p0, c0); \
      close item_constraints_no_collision(i, cs, pub); \
      leak item_constraints_no_collision(i, cs, pub); \
    } \
    else if (head(cs) == 'f') \
    { \
      assert cs == cons('f', ?cs_cg); \
      polarssl_cryptogram cg = \
                          polarssl_chars_for_cryptogram_surjective(cs_cg, 3); \
      assert cg == polarssl_public_key(?p0, ?c0); \
      polarssl_cryptograms_in_chars_public_upper_bound_split( \
                                                    polarssl_pub(pub), cs, 1); \
      polarssl_cryptogram_in_upper_bound(cs_cg, cg, \
                    polarssl_generated_public_cryptograms(polarssl_pub(pub))); \
      polarssl_generated_public_cryptograms_from(polarssl_pub(pub), cg); \
      \
      open [_]polarssl_pub(pub)(cg); \
      item i = public_key_item(p0, c0); \
      close item_constraints_no_collision(i, cs, pub); \
      leak item_constraints_no_collision(i, cs, pub); \
    } \
    else if (head(cs) == 'g') \
    { \
      assert cs == cons('g', ?cs_cg); \
      polarssl_cryptogram cg = \
                          polarssl_chars_for_cryptogram_surjective(cs_cg, 4); \
      assert cg == polarssl_private_key(?p0, ?c0); \
      polarssl_cryptograms_in_chars_public_upper_bound_split( \
                                                    polarssl_pub(pub), cs, 1); \
      polarssl_cryptograms_in_chars_split(cs, 1); \
      polarssl_cryptogram_in_upper_bound(cs_cg, cg, \
                    polarssl_generated_public_cryptograms(polarssl_pub(pub))); \
      polarssl_generated_public_cryptograms_from(polarssl_pub(pub), cg); \
      \
      open [_]polarssl_pub(pub)(cg); \
      item i = private_key_item(p0, c0); \
      close item_constraints_no_collision(i, cs, pub); \
      leak item_constraints_no_collision(i, cs, pub); \
    } \
    else if (head(cs) == 'h') \
    { \
      assert cs == cons('h', ?cs_cg); \
      polarssl_cryptogram cg = \
                           polarssl_chars_for_cryptogram_surjective(cs_cg, 6); \
      assert cg == polarssl_hmac(?p0, ?c0, ?cs_pay0); \
      polarssl_cryptograms_in_chars_public_upper_bound_split( \
                                                    polarssl_pub(pub), cs, 1); \
      polarssl_cryptogram_in_upper_bound(cs_cg, cg, \
                    polarssl_generated_public_cryptograms(polarssl_pub(pub))); \
      polarssl_generated_public_cryptograms_from(polarssl_pub(pub), cg); \
      \
      open [_]polarssl_pub(pub)(cg); \
      assert [_]exists(?col); \
      item i; \
      if (col) \
      { \
        assert [_]pub(symmetric_key_item(p0, c0)); \
        assert true == subset(polarssl_cryptograms_in_chars(cs_pay0), \
                  polarssl_generated_public_cryptograms(polarssl_pub(pub))); \
        polarssl_cryptograms_in_chars_split(cs, 1); \
        if (well_formed(cs_pay0, nat_length(cs_pay0))) \
        { \
          switch(level_bound) \
          { \
            case succ(level_bound0): \
              close proof_obligations(pub); \
              well_formed_upper_bound(cs_pay0, nat_length(cs_pay0), \
                                               nat_of_int(INT_MAX)); \
              polarssl_cryptograms_in_chars_upper_bound_to(cs_pay0, \
                                      polarssl_cryptograms_in_chars(cs_pay0)); \
              polarssl_cryptograms_in_chars_upper_bound_subset( \
                    cs_pay0, polarssl_cryptograms_in_chars(cs_pay0), \
                    polarssl_generated_public_cryptograms(polarssl_pub(pub))); \
              polarssl_cryptogram_constraints(cs_cg, cg); \
              forall_mem(cg, polarssl_cryptograms_in_chars(cs), \
                         (polarssl_cryprogram_has_lower_level) \
                         (succ(level_bound))); \
              polarssl_cryptogram_level_nested_constraints_upper_bound( \
                                                             cg, level_bound); \
              \
              assert true == well_formed(cs_pay0, nat_of_int(INT_MAX)); \
              assert true == forall( \
                   polarssl_cryptograms_in_chars(cs_pay0), \
                   (polarssl_cryprogram_has_lower_level)(succ(level_bound0))); \
              assert length(cs_pay0) <= INT_MAX; \
              assert true == polarssl_cryptograms_in_chars_upper_bound( \
                               cs_pay0, polarssl_generated_public_cryptograms( \
                                                          polarssl_pub(pub))); \
              deserialize_item_(level_bound0, nat_of_int(INT_MAX), \
                                cs_pay0, pub); \
              open [_]item_constraints_no_collision(?pay0, cs_pay0, pub); \
              open proof_obligations(pub); \
              assert [_]pub(pay0); \
              i = hmac_item(p0, c0, some(pay0)); \
              close well_formed_item_chars(i)(cs_pay0); \
              leak well_formed_item_chars(i)(cs_pay0); \
              assert is_public_hmac(?proof, pub); \
              proof(i); \
              close item_constraints_no_collision(i, cs, pub); \
              leak item_constraints_no_collision(i, cs, pub); \
            case zero: \
              polarssl_cryptogram_level_flat_constraints(cg); \
              assert polarssl_cryptogram_level(cg) != zero; \
              polarssl_cryptogram_constraints(cs_cg, cg); \
              forall_mem(cg, polarssl_cryptograms_in_chars(cs), \
                    (polarssl_cryprogram_has_lower_level)(succ(level_bound))); \
              assert polarssl_cryptogram_level(cg) == zero; \
              assert false; \
          } \
        } \
        else \
        { \
          i = hmac_item(p0, c0, none); \
          assert is_public_hmac(?proof, pub); \
          proof(i); \
          close ill_formed_item_chars(i)(cs_pay0); \
          leak ill_formed_item_chars(i)(cs_pay0); \
          close item_constraints_no_collision(i, cs, pub); \
          leak item_constraints_no_collision(i, cs, pub); \
        } \
      } \
      else \
      { \
        assert [_]item_constraints_no_collision(?pay0, cs_pay0, pub); \
        i = hmac_item(p0, c0, some(pay0)); \
        item_constraints_no_collision_well_formed(pay0, i); \
        assert [_]pub(i); \
        close item_constraints_no_collision(i, cs, pub); \
        leak item_constraints_no_collision(i, cs, pub); \
      } \
      assert [_]pub(i); \
      assert [_]item_constraints_no_collision(i, cs, pub); \
    } \
    else if (head(cs) == 'i') \
    { \
      assert cs == cons('i', ?cs0); \
      assert length(cs) <= INT_MAX; \
      list<char> ent1 = take(GCM_ENT_SIZE, cs0); \
      list<char> cs_cg = drop(GCM_ENT_SIZE, cs0); \
      polarssl_cryptograms_in_chars_split(cs, 1); \
      polarssl_cryptograms_in_chars_split(cs0, GCM_ENT_SIZE); \
      subset_trans(polarssl_cryptograms_in_chars(cs_cg), \
                   polarssl_cryptograms_in_chars(cs0), \
                   polarssl_cryptograms_in_chars(cs)); \
      assert true == subset(polarssl_cryptograms_in_chars(cs_cg), \
                            polarssl_cryptograms_in_chars(cs0)); \
      assert cs0 == append(ent1, cs_cg); \
      polarssl_cryptogram cg = \
                           polarssl_chars_for_cryptogram_surjective(cs_cg, 8); \
      assert cg == polarssl_auth_encrypted(?p0, ?c0, ?mac0, ?cs_pay0, ?iv0); \
      list<char> ent2 = cons(length(mac0), append(mac0, iv0)); \
      take_append(length(mac0), mac0, iv0); \
      drop_append(length(mac0), mac0, iv0); \
      list<char> ent3 = append(ent1, ent2); \
      take_append(GCM_ENT_SIZE, ent1, ent2); \
      drop_append(GCM_ENT_SIZE, ent1, ent2); \
      polarssl_cryptograms_in_chars_public_upper_bound_split( \
                                                    polarssl_pub(pub), cs, 1); \
      polarssl_cryptograms_in_chars_public_upper_bound_split( \
                                        polarssl_pub(pub), cs0, length(ent1)); \
      polarssl_cryptogram_in_upper_bound(cs_cg, cg, \
                    polarssl_generated_public_cryptograms(polarssl_pub(pub))); \
      polarssl_generated_public_cryptograms_from(polarssl_pub(pub), cg); \
      polarssl_cryptogram_constraints(cs_cg, cg); \
      forall_subset(polarssl_cryptograms_in_chars(cs_cg), \
                    polarssl_cryptograms_in_chars(cs), \
                    (polarssl_cryprogram_has_lower_level) \
                    (succ(level_bound))); \
      forall_mem(cg, polarssl_cryptograms_in_chars(cs_cg), \
            (polarssl_cryprogram_has_lower_level)(succ(level_bound))); \
      \
      item i; \
      open [_]polarssl_pub(pub)(cg); \
      assert [_]exists<bool>(?col); \
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
              polarssl_cryptograms_in_chars_upper_bound_to(cs_pay0, \
                                      polarssl_cryptograms_in_chars(cs_pay0)); \
              polarssl_cryptograms_in_chars_upper_bound_subset( \
                    cs_pay0, polarssl_cryptograms_in_chars(cs_pay0), \
                    polarssl_generated_public_cryptograms(polarssl_pub(pub))); \
              polarssl_cryptogram_level_nested_constraints_upper_bound( \
                                                             cg, level_bound); \
              \
              assert true == well_formed(cs_pay0, nat_of_int(INT_MAX)); \
              assert true == forall( \
                   polarssl_cryptograms_in_chars(cs_pay0), \
                   (polarssl_cryprogram_has_lower_level)(succ(level_bound0))); \
              assert length(cs_pay0) <= INT_MAX; \
              assert true == polarssl_cryptograms_in_chars_upper_bound( \
                               cs_pay0, polarssl_generated_public_cryptograms( \
                                                          polarssl_pub(pub))); \
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
              polarssl_cryptogram_level_flat_constraints(cg); \
              assert polarssl_cryptogram_level(cg) != zero; \
              assert polarssl_cryptogram_level(cg) == zero; \
              assert false; \
          } \
        } \
        else \
        { \
          i = symmetric_encrypted_item(p0, c0, none, ent3); \
          assert is_public_symmetric_encrypted(?proof, pub); \
          proof(i); \
          close ill_formed_item_chars(i)(cs_pay0); \
          leak ill_formed_item_chars(i)(cs_pay0); \
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
      }\
      assert [_]pub(i); \
      close symmetric_encryption_entropy(i)(mac0, iv0); \
      leak symmetric_encryption_entropy(i)(mac0, iv0); \
      close item_constraints_no_collision(i, cs, pub); \
      leak item_constraints_no_collision(i, cs, pub); \
    } \
    else if (head(cs) == 'j') \
    { \
      assert cs == cons('j', ?cs_cg); \
      polarssl_cryptogram cg = \
                           polarssl_chars_for_cryptogram_surjective(cs_cg, 9); \
      assert cg == polarssl_asym_encrypted(?p0, ?c0, ?cs_pay0, ?ent0); \
      polarssl_cryptograms_in_chars_split(cs, 1); \
      polarssl_cryptograms_in_chars_public_upper_bound_split( \
                                                    polarssl_pub(pub), cs, 1); \
      polarssl_cryptogram_in_upper_bound(cs_cg, cg, \
                    polarssl_generated_public_cryptograms(polarssl_pub(pub))); \
      polarssl_generated_public_cryptograms_from(polarssl_pub(pub), cg); \
      \
      polarssl_cryptogram_constraints(cs_cg, cg); \
      forall_subset(polarssl_cryptograms_in_chars(cs_cg), \
                    polarssl_cryptograms_in_chars(cs), \
                    (polarssl_cryprogram_has_lower_level) \
                    (succ(level_bound))); \
      forall_mem(cg, polarssl_cryptograms_in_chars(cs_cg), \
            (polarssl_cryprogram_has_lower_level)(succ(level_bound))); \
      \
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
              well_formed_upper_bound(cs_pay0, nat_length(cs_pay0), \
                                               nat_of_int(INT_MAX)); \
              polarssl_cryptograms_in_chars_upper_bound_to(cs_pay0, \
                                      polarssl_cryptograms_in_chars(cs_pay0)); \
              polarssl_cryptograms_in_chars_upper_bound_subset( \
                    cs_pay0, polarssl_cryptograms_in_chars(cs_pay0), \
                    polarssl_generated_public_cryptograms(polarssl_pub(pub))); \
              polarssl_cryptogram_level_nested_constraints_upper_bound( \
                                                             cg, level_bound); \
              \
              assert true == well_formed(cs_pay0, nat_of_int(INT_MAX)); \
              assert true == forall( \
                   polarssl_cryptograms_in_chars(cs_pay0), \
                   (polarssl_cryprogram_has_lower_level)(succ(level_bound0))); \
              assert length(cs_pay0) <= INT_MAX; \
              assert true == polarssl_cryptograms_in_chars_upper_bound( \
                               cs_pay0, polarssl_generated_public_cryptograms( \
                                                          polarssl_pub(pub))); \
              deserialize_item_(level_bound0, nat_of_int(INT_MAX), \
                                cs_pay0, pub); \
              assert [_]item_constraints_no_collision(?pay0, cs_pay0, pub); \
              open proof_obligations(pub); \
              assert [_]pub(pay0); \
              i = asymmetric_encrypted_item(p0, c0, some(pay0), ent0); \
              close well_formed_item_chars(i)(cs_pay0); \
              leak well_formed_item_chars(i)(cs_pay0); \
              assert is_public_asymmetric_encrypted(?proof, pub); \
              proof(i); \
            case zero: \
              polarssl_cryptogram_level_flat_constraints(cg); \
              assert polarssl_cryptogram_level(cg) != zero; \
              assert polarssl_cryptogram_level(cg) == zero; \
              assert false; \
          } \
        } \
        else \
        { \
          i = asymmetric_encrypted_item(p0, c0, none, ent0); \
          assert is_public_asymmetric_encrypted(?proof, pub); \
          proof(i); \
          close ill_formed_item_chars(i)(cs_pay0); \
          leak ill_formed_item_chars(i)(cs_pay0); \
        } \
      } \
      else \
      { \
        assert [_]item_constraints_no_collision(?pay0, cs_pay0, pub); \
        i = asymmetric_encrypted_item(p0, c0, some(pay0), ent0); \
        assert [_]pub(i); \
        item_constraints_no_collision_well_formed(pay0, i); \
      } \
      assert [_]pub(i); \
      close item_constraints_no_collision(i, cs, pub); \
      leak item_constraints_no_collision(i, cs, pub); \
    } \
    else if (head(cs) == 'k') \
    { \
      assert cs == cons('k', ?cs_cg); \
      polarssl_cryptogram cg = \
                          polarssl_chars_for_cryptogram_surjective(cs_cg, 10); \
      assert cg == polarssl_asym_signature(?p0, ?c0, ?cs_pay0, ?ent0); \
      polarssl_cryptograms_in_chars_split(cs, 1); \
      polarssl_cryptograms_in_chars_public_upper_bound_split( \
                                                    polarssl_pub(pub), cs, 1); \
      polarssl_cryptogram_in_upper_bound(cs_cg, cg, \
                    polarssl_generated_public_cryptograms(polarssl_pub(pub))); \
      polarssl_generated_public_cryptograms_from(polarssl_pub(pub), cg); \
      \
      polarssl_cryptogram_constraints(cs_cg, cg); \
      forall_subset(polarssl_cryptograms_in_chars(cs_cg), \
                    polarssl_cryptograms_in_chars(cs), \
                    (polarssl_cryprogram_has_lower_level) \
                    (succ(level_bound))); \
      forall_mem(cg, polarssl_cryptograms_in_chars(cs_cg), \
            (polarssl_cryprogram_has_lower_level)(succ(level_bound))); \
      \
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
              well_formed_upper_bound(cs_pay0, nat_length(cs_pay0), \
                                               nat_of_int(INT_MAX)); \
              polarssl_cryptograms_in_chars_upper_bound_to(cs_pay0, \
                                      polarssl_cryptograms_in_chars(cs_pay0)); \
              polarssl_cryptograms_in_chars_upper_bound_subset( \
                    cs_pay0, polarssl_cryptograms_in_chars(cs_pay0), \
                    polarssl_generated_public_cryptograms(polarssl_pub(pub))); \
              polarssl_cryptogram_level_nested_constraints_upper_bound( \
                                                             cg, level_bound); \
              \
              assert true == well_formed(cs_pay0, nat_of_int(INT_MAX)); \
              assert true == forall( \
                   polarssl_cryptograms_in_chars(cs_pay0), \
                   (polarssl_cryprogram_has_lower_level)(succ(level_bound0))); \
              assert length(cs_pay0) <= INT_MAX; \
              assert true == polarssl_cryptograms_in_chars_upper_bound( \
                               cs_pay0, polarssl_generated_public_cryptograms( \
                                                          polarssl_pub(pub))); \
              deserialize_item_(level_bound0, nat_of_int(INT_MAX), \
                                cs_pay0, pub); \
              assert [_]item_constraints_no_collision(?pay0, cs_pay0, pub); \
              open proof_obligations(pub); \
              assert [_]pub(pay0); \
              i = asymmetric_signature_item(p0, c0, some(pay0), ent0); \
              close well_formed_item_chars(i)(cs_pay0); \
              leak well_formed_item_chars(i)(cs_pay0); \
              assert is_public_asymmetric_signature(?proof, pub); \
              proof(i); \
            case zero: \
              polarssl_cryptogram_level_flat_constraints(cg); \
              assert polarssl_cryptogram_level(cg) != zero; \
              assert polarssl_cryptogram_level(cg) == zero; \
              assert false; \
          } \
        } \
        else \
        { \
          i = asymmetric_signature_item(p0, c0, none, ent0); \
          assert is_public_asymmetric_signature(?proof, pub); \
          proof(i); \
          close ill_formed_item_chars(i)(cs_pay0); \
          leak ill_formed_item_chars(i)(cs_pay0); \
        } \
      } \
      else \
      { \
        assert [_]item_constraints_no_collision(?pay0, cs_pay0, pub); \
        i = asymmetric_signature_item(p0, c0, some(pay0), ent0); \
        assert [_]pub(i); \
        item_constraints_no_collision_well_formed(pay0, i); \
      } \
      assert [_]pub(i); \
      close item_constraints_no_collision(i, cs, pub); \
      leak item_constraints_no_collision(i, cs, pub); \
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
                   (polarssl_cryprogram_has_lower_level)(succ(level_bound))) &*&
           //knowledge about second inductive paramter
           length(cs) <= int_of_nat(length_bound) &*&
           true == well_formed(cs, length_bound) &*&
           true == polarssl_cryptograms_in_chars_upper_bound(
               cs, polarssl_generated_public_cryptograms(polarssl_pub(pub)));
  ensures  proof_obligations(pub) &*&
           [_]item_constraints_no_collision(?i, cs, pub) &*& [_]pub(i);
{
  //Dummy switch to enforce lexicographic induction
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
           true == polarssl_cryptograms_in_chars_upper_bound(
               cs, polarssl_generated_public_cryptograms(polarssl_pub(pub)));
  ensures  proof_obligations(pub) &*&
           [_]item_constraints_no_collision(?i, cs, pub) &*& [_]pub(i);
{
  well_formed_upper_bound(cs, nat_length(cs), nat_of_int(INT_MAX));
  polarssl_cryptograms_in_chars_upper_bound_from(cs, 
                  polarssl_generated_public_cryptograms(polarssl_pub(pub)));
  polarssl_cryptograms_in_chars_generated(polarssl_pub(pub), cs);
  polarssl_cryptograms_generated_level_upper_bound(
                                         polarssl_cryptograms_in_chars(cs));
  deserialize_item_(polarssl_cryprogram_level_upper_bound(), 
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
  memcpy(buffer_s, message + 1 + (int) sizeof(int) + size_f, (unsigned int) size_s);
  //@ assert chars(buffer_s, size_s, ?cs_s);
  if (size_f <= 1 || size_s <= 1)
    abort_crypto_lib("Incorrect size for pair item");
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
  if (size <= 1){abort_crypto_lib("Found corrupted item during deserialization");}
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
