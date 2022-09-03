#ifndef NSL_H
#define NSL_H

#include "../../annotated_api/mbedTLS_definitions.h"

#define NONCE_SIZE 16
#define KEY_SIZE 128

#define MSG1_SIZE 28 //should be ID_SIZE + NONCE_SIZE
#define MSG2_SIZE 44 //should be ID_SIZE + 2 * NONCE_SIZE
#define MSG3_SIZE 16 //should be NONCE_SIZE

/*@

// 1. A -> B. {A,NA}_K(B)
// 2. B -> A. {B,NA,NB}_K(A)
// 3. A -> B. {NB}_K(B)

//or

// 1. sender -> receiver : ASYM_ENC(K(receiver),
//                           {NAME(sender), NONCE(sender)})
// 2. receiver -> sender : ASYM_ENC(K(sender),
//                           {NAME(receiver), NONCE(sender), NONCE(receiver)})
// 3. sender -> receiver : ASYM_ENC(K(receiver),
//                           {NONCE(receiver)})

///////////////////////////////////////////////////////////////////////////////
// Encodings for this protocol ////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

// info:
// int_pair(1, int_pair(receiver, r_id)): sender nonce
// int_pair(2, int_pair(sender, int_pair(p_inst,
//                              int_pair(p_orig, c_orig))): receiver nonce

///////////////////////////////////////////////////////////////////////////////
// Definition of pub for this protocol ////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

predicate nsl_pub_msg_sender(int sender) = true;

predicate nsl_pub_msg1(int sender, int receiver, cryptogram s_nonce) = true;

predicate nsl_pub_msg2(int sender, int receiver, cryptogram s_nonce,
                       list<crypto_char> s_nonce_ccs, cryptogram r_nonce,
                       int p_inst, int p_orig, int c_orig, bool pub_ns) = true;

predicate nsl_pub_msg3(int sender, int receiver, cryptogram r_nonce) = true;

predicate nsl_proof_pred() =
  exists(?attacker) &*& true == bad(attacker)
;

fixpoint bool nsl_public_nonce(int principal, int info)
{
  return
    col || bad(principal) ||
    (int_left(info) == 1 && bad(int_left(int_right(info)))) ||
    (int_left(info) == 2 && bad(int_left(int_right(info))));
}

fixpoint bool nsl_public_key(int p, int c, bool symmetric)
{
  return bad(p);
}

predicate nsl_pub(cryptogram cg) =
  switch (cg)
  {
    case cg_nonce(p0, c0):
      return true == nsl_public_nonce(p0, cg_info(cg));
    case cg_symmetric_key(p0, c0):
      return true == nsl_public_key(p0, c0, true);
    case cg_rsa_public_key(p0, c0):
      return true;
    case cg_rsa_private_key(p0, c0):
      return true == nsl_public_key(p0, c0, false);
    case cg_sha512_hash(ccs0):
      return true;
    case cg_sha512_hmac(p0, c0, ccs0):
      return true;
    case cg_aes_encrypted(p0, c0, ccs0, ent0):
      return true == nsl_public_key(p0, c0, true) &*&
             [_]public_ccs(ccs0);
    case cg_aes_auth_encrypted(p0, c0, ccs0, ent0):
      return true == nsl_public_key(p0, c0, true) &*&
             [_]public_ccs(ccs0);
    case cg_rsa_encrypted(p0, c0, ccs0, ent0):
      return [_]nsl_pub_msg_sender(?p1) &*&
      col || bad(p0) || bad(p1) ?
        [_]public_ccs(ccs0)
      :
      (
        length(ccs0) == MSG1_SIZE ?
        (
          // 1. A -> B. {A,NA}_K(B)
          nsl_pub_msg1(?sender, ?receiver, ?s_nonce) &*&
          p1 == sender && p0 == receiver &*&
          ccs0 == append(cs_to_ccs(identifier(sender)),
                         ccs_for_cg(s_nonce)) &*&
          [_]public_ccs(take(ID_SIZE, ccs0)) &*&
          length(identifier(sender)) == ID_SIZE &*&
          length(cs_to_ccs(identifier(sender))) == ID_SIZE &*&
          s_nonce == cg_nonce(sender, _) &*&
          cg_info(s_nonce) == int_pair(1, int_pair(p0, c0)) &*&
          true == cg_is_gen_or_pub(s_nonce)
        )
      : length(ccs0) == MSG2_SIZE ?
        (
          // 2. B -> A. {B,NA,NB}_K(A)
          nsl_pub_msg2(?sender, ?receiver, ?s_nonce, ?s_nonce_ccs, ?r_nonce,
                       ?p_inst, ?p_orig, ?c_orig, ?pub_ns) &*&
          p1 == receiver && p0 == sender &*&
          ccs0 == append(cs_to_ccs(identifier(receiver)),
                         append(s_nonce_ccs, ccs_for_cg(r_nonce))) &*&
          [_]public_ccs(take(ID_SIZE, ccs0)) &*&
          r_nonce == cg_nonce(receiver, _) &*&
          cg_info(r_nonce) == int_pair(2, int_pair(sender, int_pair(p_inst,
                                          int_pair(p_orig, c_orig)))) &*&
          true == cg_is_gen_or_pub(r_nonce) &*&
          length(s_nonce_ccs) == NONCE_SIZE &*&
          length(identifier(receiver)) == ID_SIZE &*&
          length(cs_to_ccs(identifier(receiver))) == ID_SIZE &*&
          pub_ns ?
            [_]public_ccs(s_nonce_ccs)
          :
            s_nonce_ccs == ccs_for_cg(s_nonce) &*&
            s_nonce == cg_nonce(sender, _) &*&
            c_orig == int_right(int_right(cg_info(s_nonce))) &*&
            cg_is_gen_or_pub(s_nonce) &&
            p_inst == sender && p_orig == receiver
        )
      : length(ccs0) == MSG3_SIZE ?
          // 3. A -> B. {NB}_K(B)
          nsl_pub_msg3(?sender, ?receiver, ?r_nonce) &*&
          p1 == sender &*& p0 == receiver &*&
          r_nonce == cg_nonce(receiver, _) &*&
          ccs0 == ccs_for_cg(r_nonce) &*&
          cg_info(r_nonce) == int_pair(2, int_pair(sender, int_pair(sender,
                                          int_pair(p0, c0)))) &*&
          true == cg_is_gen_or_pub(r_nonce)
      :
          false
      );
    case cg_rsa_signature(p0, c0, ccs0, ent0):
      return true == nsl_public_key(p0, c0, false);
  }
;

@*/

///////////////////////////////////////////////////////////////////////////////
// Implementation prototypes for this protocol ////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

void sender(int sender, int receiver,
            char *s_priv_key, char *r_pub_key,
            char *s_nonce, char *r_nonce);
/*@ requires [_]public_invar(nsl_pub) &*&
             [_]decryption_key_classifier(nsl_public_key) &*&
             principal(sender, _) &*&
             [?f1]cryptogram(s_priv_key, 8 * KEY_SIZE,
                             ?s_priv_key_ccs, ?s_priv_key_cg) &*&
               s_priv_key_cg == cg_rsa_private_key(sender, ?s_id) &*&
             [?f2]cryptogram(r_pub_key, 8 * KEY_SIZE,
                             ?r_pub_key_ccs, ?r_pub_key_cg) &*&
               r_pub_key_cg == cg_rsa_public_key(receiver, ?r_id) &*&
             chars_(s_nonce, NONCE_SIZE, _) &*&
             chars_(r_nonce, NONCE_SIZE, _); @*/
/*@ ensures  principal(sender, _) &*&
             [f1]cryptogram(s_priv_key, 8 * KEY_SIZE,
                            s_priv_key_ccs, s_priv_key_cg) &*&
             [f2]cryptogram(r_pub_key, 8 * KEY_SIZE,
                            r_pub_key_ccs, r_pub_key_cg) &*&
             cryptogram(s_nonce, NONCE_SIZE, ?s_nonce_ccs, ?s_nonce_cg) &*&
               s_nonce_cg == cg_nonce(sender, _) &*&
               cg_info(s_nonce_cg) == int_pair(1, int_pair(receiver, r_id)) &*&
             col || bad(sender) || bad(receiver) ?
               chars(r_nonce, NONCE_SIZE, _)
             :
               cryptogram(r_nonce, NONCE_SIZE, _, ?r_nonce_cg) &*&
               r_nonce_cg == cg_nonce(receiver, _) &*&
               cg_info(r_nonce_cg) == int_pair(2, int_pair(sender, int_pair(sender,
                                                  int_pair(receiver, r_id)))); @*/

void receiver(int sender, int receiver,
              char *s_pub_key, char *r_priv_key,
              char *s_nonce, char *r_nonce);
/*@ requires [_]public_invar(nsl_pub) &*&
             [_]decryption_key_classifier(nsl_public_key) &*&
             principal(receiver, _) &*&
             [?f1]cryptogram(s_pub_key, 8 * KEY_SIZE,
                             ?s_pub_key_ccs, ?s_pub_key_cg) &*&
               s_pub_key_cg == cg_rsa_public_key(sender, ?s_id) &*&
             [?f2]cryptogram(r_priv_key, 8 * KEY_SIZE,
                             ?r_priv_key_ccs, ?r_priv_key_cg) &*&
               r_priv_key_cg == cg_rsa_private_key(receiver, ?r_id) &*&
             chars_(s_nonce, NONCE_SIZE, _) &*&
             chars_(r_nonce, NONCE_SIZE, _); @*/
/*@ ensures  principal(receiver, _) &*&
             [f1]cryptogram(s_pub_key, 8 * KEY_SIZE,
                            s_pub_key_ccs, s_pub_key_cg) &*&
             [f2]cryptogram(r_priv_key, 8 * KEY_SIZE,
                            r_priv_key_ccs, r_priv_key_cg) &*&
             cryptogram(r_nonce, NONCE_SIZE, ?r_nonce_ccs, ?r_nonce_cg) &*&
               r_nonce_cg == cg_nonce(receiver, _) &*&
             (
               col || bad(sender) || bad(receiver) ?
                 chars(s_nonce, NONCE_SIZE, _)
               :
                 cryptogram(s_nonce, NONCE_SIZE, ?s_nonce_ccs, ?s_nonce_cg) &*&
                 s_nonce_cg == cg_nonce(sender, _) &*&
                 cg_info(s_nonce_cg) == int_pair(1, int_pair(receiver, r_id)) &*&
                 cg_info(r_nonce_cg) == int_pair(2, int_pair(sender, int_pair(sender,
                                                    int_pair(receiver, r_id))))
             ); @*/

///////////////////////////////////////////////////////////////////////////////
// Attacker proof obligations for this protocol ///////////////////////////////
///////////////////////////////////////////////////////////////////////////////

/*@
DEFAULT_IS_PUBLIC_NONCE(nsl)
DEFAULT_IS_PUBLIC_KEY(nsl)
DEFAULT_IS_PUBLIC_PUBLIC_KEY(nsl)
DEFAULT_IS_PUBLIC_PRIVATE_KEY(nsl)
DEFAULT_IS_PUBLIC_HASH(nsl)
DEFAULT_IS_PUBLIC_HMAC(nsl)
DEFAULT_IS_PUBLIC_ENCRYPTED(nsl)
DEFAULT_IS_PUBLIC_DECRYPTED(nsl)
DEFAULT_IS_PUBLIC_AUTH_ENCRYPTED(nsl)
DEFAULT_IS_PUBLIC_AUTH_DECRYPTED(nsl)
// DEFAULT_IS_PUBLIC_ASYMMETRIC_ENCRYPTED(nsl)
// DEFAULT_IS_PUBLIC_ASYMMETRIC_DECRYPTED(nsl)
DEFAULT_IS_PUBLIC_ASYMMETRIC_SIGNATURE(nsl)
DECRYPTION_PROOFS(nsl)

lemma void public_asym_encryption_is_public(cryptogram encrypted)
  requires nsl_proof_pred() &*&
           encrypted == cg_rsa_encrypted(?p, ?c, ?pay, ?ent) &*&
           [_]nsl_pub(cg_rsa_public_key(p, c)) &*&
           [_]public_ccs(pay);
  ensures  nsl_proof_pred() &*&
           [_]nsl_pub(encrypted);
{
  open  [_]nsl_pub(cg_rsa_public_key(p, c));
  POLARSSL_SWITCH_1(PREFIX, cg_rsa_public_key(p, c));
  open nsl_proof_pred();
  assert exists(?attacker);
  close nsl_proof_pred();
  close nsl_pub_msg_sender(attacker);
  leak nsl_pub_msg_sender(attacker);
  close nsl_pub(encrypted);
  leak nsl_pub(encrypted);
}

lemma void public_asym_decryption_is_public(cryptogram key,
                                            cryptogram encrypted)
  requires key == cg_rsa_private_key(?p, ?c) &*&
           encrypted == cg_rsa_encrypted(p, c, ?pay, ?ent) &*&
           [_]nsl_pub(key) &*&
           [_]nsl_pub(encrypted);
  ensures  [_]public_ccs(pay);
{
  open  [_]nsl_pub(key);
  open  [_]nsl_pub(encrypted);

  POLARSSL_SWITCH_1(PREFIX, cg_rsa_private_key(p, c));
  assert true == bad(p);
}

@*/

#endif
