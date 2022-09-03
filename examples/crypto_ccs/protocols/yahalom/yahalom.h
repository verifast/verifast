#ifndef YAHALOM_H
#define YAHALOM_H

#include "../../annotated_api/mbedTLS_definitions.h"

#define KEY_SIZE 32
#define NONCE_SIZE 10

/*@

// 1. A -> B. A, NA
// 2. B -> S. B, ENC(KB, {A, NA, NB})
// 3. S -> A. ENC(KA, {B, KAB, NA, NB}), ENC(KB, {A, KAB})
// 4. A -> B. ENC(KB, {A, KAB}), ENC(KAB, NB)

// 1. sender -> receiver : NAME(sender), NONCE(sender)
// 2. receiver -> server : NAME(receiver),
//                         ENC(K(receiver),
//                           {NAME(sender), NONCE(sender), NONCE(receiver)}
//                         )
// 3. server -> sender   : ENC(K(sender),
//                           {NAME(receiver), KEY(server),
//                            NONCE(sender), NONCE(receiver)}
//                         )
//                         ENC(K(receiver),
//                           {NAME(sender), KEY(server)}
//                          )
// 4. sender -> receiver : ENC(K(receiver),
//                           {NAME(sender), KEY(server)}
//                         )
//                         ENC(K(server), NONCE(receiver))

///////////////////////////////////////////////////////////////////////////////
// Encodings for this protocol ////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

#define IP(F, S) int_pair(F, S)
#define IF(I) int_left(I)
#define IS(I) int_right(I)

// info:
//  IP(0, _):                                                   no information
//  IP(1, receiver):                                            sender nonce
//  IP(2, IP(server, IP(sender, IP(s, s_id)))):                 receiver nonce
//  IP(3, server):                                              server key
//  IP(4, IP(sender, IP(receiver
//        IP(s, IP(s_id, IP(r, r_id)))))):                      generated key

///////////////////////////////////////////////////////////////////////////////
// Definition of pub for this protocol ////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

fixpoint bool yahalom_public_nonce(int principal, int info)
{
  return
    bad(principal) ||
    IF(info) == 0 ||
    IF(info) == 1 ||
   (IF(info) == 2 &&
      (bad(IF(IS(info))) ||
       bad(IF(IS(IS(info))))));
}

fixpoint bool yahalom_public_key_(int principal, int info)
{
  return
    bad(principal) ||
   (IF(info) == 3 && bad(IS(info))) ||
   (IF(info) == 4 &&
     (bad(IF(IS(info))) || bad(IF(IS(IS(info))))));
}

fixpoint bool yahalom_public_key(int principal, int count, bool sym)
{
  return sym ? 
           yahalom_public_key_(principal,
                               cg_info(cg_symmetric_key(principal, count)))
         :
           bad(principal);
}

predicate yahalom_proof_pred() = true;

predicate yahalom_pub_msg1(int server, int sender,
                           cryptogram NA, cryptogram NB) = true;
predicate yahalom_pub_msg2(int sender, int receiver, cryptogram NA,
                           cryptogram NB, cryptogram KAB) = true;
predicate yahalom_pub_msg3(int server, int sender, cryptogram KAB,
                           int sendr2, int a_id, int receivr2, int b_id) = true;
predicate yahalom_pub_msg4(int server, int sender, int receiver,
                           int a_id, cryptogram NB) = true;

predicate yahalom_pub(cryptogram cg) =
  switch (cg)
  {
    case cg_nonce(p0, c0):
      return true == yahalom_public_nonce(p0, cg_info(cg));
    case cg_symmetric_key(p0, c0):
      return true == yahalom_public_key(p0, c0, true);
    case cg_rsa_public_key(p0, c0):
      return true;
    case cg_rsa_private_key(p0, c0):
      return true == yahalom_public_key(p0, c0, false);
    case cg_sha512_hash(ccs0):
      return true;
    case cg_sha512_hmac(p0, c0, ccs0):
      return true;
    case cg_aes_encrypted(p0, c0, ccs0, ent0):
      return yahalom_public_key(p0, c0, true) ?
        [_]public_ccs(ccs0)
      :
        length(ccs0) == ID_SIZE + NONCE_SIZE + NONCE_SIZE ?
        (
          // ENC(KB, {A, NA, NB})
          yahalom_pub_msg1(?server, ?sender, ?NA, ?NB) &*&
          cg_info(cg_symmetric_key(p0, c0)) == IP(3, server) &*&
          NA == cg_nonce(?sender2, ?a_id) &*&
          true == cg_is_gen_or_pub(NA) &*& [_]yahalom_pub(NA) &*&
          NB == cg_nonce(p0, _) &*& true == cg_is_gen_or_pub(NB) &*&
          cg_info(NB) == IP(2, IP(server, IP(sender, IP(sender2, a_id)))) &*&
          length(identifier(sender)) == ID_SIZE &*&
          length(cs_to_ccs(identifier(sender))) == ID_SIZE &*&
          length(ccs_for_cg(NA)) == NONCE_SIZE &*&
          length(ccs_for_cg(NB)) == NONCE_SIZE &*&
          ccs0 == append(cs_to_ccs(identifier(sender)),
                         append(ccs_for_cg(NA), ccs_for_cg(NB))) &*&
          [_]public_ccs(cs_to_ccs(identifier(sender)))
        ) :
        length(ccs0) == ID_SIZE + KEY_SIZE + NONCE_SIZE + NONCE_SIZE ?
        (
          // ENC(KA, {B, KAB, NA, NB})
          yahalom_pub_msg2(?server, ?receiver, ?NA, ?NB, ?KAB) &*&
          cg_info(cg_symmetric_key(p0, c0)) == IP(3, server) &*&
          NA == cg_nonce(?sender2, ?a_id) &*&
          true == cg_is_gen_or_pub(NA) &*& [_]yahalom_pub(NA) &*&
          NB == cg_nonce(?receiver2, ?b_id) &*&
          (
          bad(server) || bad(receiver) ?
            [_]yahalom_pub(NB)
          :
            (cg_info(NB) == IP(2, IP(server, IP(p0, IP(sender2, a_id)))) &&
             receiver == receiver2)
          ) &*&
          true == cg_is_gen_or_pub(NB) &*&
          KAB == cg_symmetric_key(server, _) &*&
          true == cg_is_gen_or_pub(KAB) &*&
          cg_info(KAB) == IP(4, IP(p0, IP(receiver,
                            IP(sender2, IP(a_id, IP(receiver2, b_id)))))) &*&
          length(identifier(receiver)) == ID_SIZE &*&
          length(cs_to_ccs(identifier(receiver))) == ID_SIZE &*&
          length(ccs_for_cg(KAB)) == KEY_SIZE &*&
          length(ccs_for_cg(NA)) == NONCE_SIZE &*&
          length(ccs_for_cg(NB)) == NONCE_SIZE &*&
          ccs0 == append(cs_to_ccs(identifier(receiver)), append(ccs_for_cg(KAB),
                  append(ccs_for_cg(NA), ccs_for_cg(NB)))) &*&
          [_]public_ccs(cs_to_ccs(identifier(receiver)))
        ) :
        length(ccs0) == ID_SIZE + KEY_SIZE ?
        (
          // ENC(KB, {A, KAB})
          yahalom_pub_msg3(?server, ?sender, ?KAB, ?sender2, ?a_id,
                                                   ?receiver2, ?b_id) &*&
          cg_info(cg_symmetric_key(p0, c0)) == IP(3, server) &*&
          KAB == cg_symmetric_key(server, _) &*&
          cg_info(KAB) == IP(4, IP(sender, IP(p0,
                            IP(sender2, IP(a_id, IP(receiver2, b_id)))))) &*&
          true == cg_is_gen_or_pub(KAB) &*&
          length(identifier(sender)) == ID_SIZE &*&
          length(cs_to_ccs(identifier(sender))) == ID_SIZE &*&
          length(ccs_for_cg(KAB)) == KEY_SIZE &*&
          ccs0 == append(cs_to_ccs(identifier(sender)), ccs_for_cg(KAB)) &*&
          [_]public_ccs(cs_to_ccs(identifier(sender)))
        ) :
        length(ccs0) == NONCE_SIZE ?
        (
          // ENC(KAB, NB)
          yahalom_pub_msg4(?server, ?sender, ?receiver, ?a_id, ?NB) &*&
          NB == cg_nonce(?receiver2, ?b_id) &*&
          ccs0 == ccs_for_cg(NB) &*&
          true == cg_is_gen_or_pub(NB) &*&
          (
             bad(server) || bad(sender) || bad(receiver) ?
              [_]yahalom_pub(NB)
            :
              receiver == receiver2 &*&
              p0 == server &*&
              cg_info(NB) ==
                IP(2, IP(p0, IP(sender, IP(sender, a_id)))) &*&
              cg_info(cg_symmetric_key(p0, c0)) ==
                IP(4, IP(sender, IP(receiver, IP(sender, IP(a_id,
                                              IP(receiver2, b_id))))))
          )
        ) :
        false;
    case cg_aes_auth_encrypted(p0, c0, ccs0, ent0):
      return true == yahalom_public_key(p0, c0, true) &*&
             [_]public_ccs(ccs0);
    case cg_rsa_encrypted(p0, c0, ccs0, ent0):
      return [_]public_ccs(ccs0);
    case cg_rsa_signature(p0, c0, ccs0, ent0):
      return true == yahalom_public_key(p0, c0, false);
  }
;

@*/

///////////////////////////////////////////////////////////////////////////////
// Implementation prototypes for this protocol ////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

void server(int server, int sender, int receiver,
            char *s_key, char *r_key);
/*@ requires [_]public_invar(yahalom_pub) &*&
             [_]decryption_key_classifier(yahalom_public_key) &*&
             principal(server, _) &*&
             [?f1]cryptogram(s_key, KEY_SIZE, ?s_key_ccs, ?s_key_cg) &*&
               s_key_cg == cg_symmetric_key(sender, _) &*&
               cg_info(s_key_cg) == IP(3, server) &*&
             [?f2]cryptogram(r_key, KEY_SIZE, ?r_key_ccs, ?r_key_cg) &*&
               r_key_cg == cg_symmetric_key(receiver, _) &*&
               cg_info(r_key_cg) == IP(3, server); @*/
/*@ ensures  principal(server, _) &*&
             [f1]cryptogram(s_key, KEY_SIZE, s_key_ccs, s_key_cg) &*&
             [f2]cryptogram(r_key, KEY_SIZE, r_key_ccs, r_key_cg); @*/

void sender(int server, int sender, int receiver,
            char *key, char *generated_key);
/*@ requires [_]public_invar(yahalom_pub) &*&
             [_]decryption_key_classifier(yahalom_public_key) &*&
             principal(sender, ?s_id) &*&
             [?f]cryptogram(key, KEY_SIZE, ?key_ccs, ?key_cg) &*&
               key_cg == cg_symmetric_key(sender, _) &*&
               cg_info(key_cg) == IP(3, server) &*&
             chars_(generated_key, KEY_SIZE, _); @*/
/*@ ensures  principal(sender, _) &*&
             [f]cryptogram(key, KEY_SIZE, key_ccs, key_cg) &*&
             cryptogram(generated_key, KEY_SIZE, _, ?g_key_cg) &*&
             col || bad(server) || bad(sender) ?
               true
             :
               g_key_cg == cg_symmetric_key(server, ?id) &*&
               IF(cg_info(g_key_cg)) == 4 &*&
               IF(IS(cg_info(g_key_cg))) == sender &*&
               IF(IS(IS(cg_info(g_key_cg)))) == receiver &*&
               IF(IS(IS(IS(cg_info(g_key_cg))))) == sender &*&
               IF(IS(IS(IS(IS(cg_info(g_key_cg)))))) ==  s_id + 1 &*&
               bad(receiver) ||
                 IF(IS(IS(IS(IS(IS(cg_info(g_key_cg))))))) == receiver &&
                 !yahalom_public_key(server, id, true); @*/

void receiver(int server, int sender, int receiver,
              char *key, char *generated_key);
/*@ requires [_]public_invar(yahalom_pub) &*&
             [_]decryption_key_classifier(yahalom_public_key) &*&
             principal(receiver, ?r_id) &*&
             [?f]cryptogram(key, KEY_SIZE, ?key_ccs, ?key_cg) &*&
               key_cg == cg_symmetric_key(receiver, _) &*&
               cg_info(key_cg) == IP(3, server) &*&
             chars_(generated_key, KEY_SIZE, _); @*/
/*@ ensures  principal(receiver, _) &*&
             [f]cryptogram(key, KEY_SIZE, key_ccs, key_cg) &*&
             cryptogram(generated_key, KEY_SIZE, _, ?g_key_cg) &*&
             col || bad(server) || bad(sender) || bad(receiver) ?
               true
             :
               g_key_cg == cg_symmetric_key(server, ?id) &*&
               IF(cg_info(g_key_cg)) == 4 &*&
               IF(IS(cg_info(g_key_cg))) == sender &*&
               IF(IS(IS(cg_info(g_key_cg)))) == receiver &*&
               IF(IS(IS(IS(cg_info(g_key_cg))))) == sender &*&
               IF(IS(IS(IS(IS(IS(cg_info(g_key_cg))))))) == receiver &*&
               IS(IS(IS(IS(IS(IS(cg_info(g_key_cg))))))) == r_id + 1; @*/

///////////////////////////////////////////////////////////////////////////////
// Attacker proof obligations for this protocol ///////////////////////////////
///////////////////////////////////////////////////////////////////////////////

//@ PUBLIC_INVARIANT_PROOFS(yahalom)
//@ DECRYPTION_PROOFS(yahalom)

#endif
