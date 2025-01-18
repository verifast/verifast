#ifndef OTWAY_REES_H
#define OTWAY_REES_H

#include "../../include/symbolic.h"

#define INITIAL_MSG -1

/*@

///////////////////////////////////////////////////////////////////////////////
// Encodings for this protocol ////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

///////////////////////////////////////////////////////////////////////////////
// Definition of pub for this protocol ////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

fixpoint bool ror_public_sym_key(int principal, int info)
{
  return bad(principal) ||
         int_left(info) == 0 &&
         (
           bad(int_right(info))
         ) ||
         int_left(info) == 1 &&
         (
           bad(int_left(int_right(info))) ||
           bad(int_right(int_right(info)))
         );
}

fixpoint bool ror_key_clsfy(int p, int c, bool sym)
{
  return sym ?
           ror_public_sym_key(p, info_for_item(symmetric_key_item(p, c)))
         :
           bad(p);
}

predicate ror_pub_pred_hmac(int current, item pay, int k_info,
                            int server, int previous, int next) =
  k_info == int_pair(0, server) &*&
  pay == pair_item(data_item(chars_of_int(current)),
           pair_item(data_item(chars_of_int(next)),
                     pair_item(?nonce, ?rest))) &*&
  INT_MIN <= previous && previous <= INT_MAX &*&
  INT_MIN <= next && next <= INT_MAX &*&
  nonce == nonce_item(current, _, 0) &*&
  info_for_item(nonce) == int_pair(previous, next) &*&
  [_]ror_pub(rest) &*&
  rest == data_item(chars_of_int(INITIAL_MSG)) ?
    previous == INITIAL_MSG
  :
    rest == 
      pair_item(
        pair_item(data_item(chars_of_int(previous)),
          pair_item(data_item(chars_of_int(current)), _)), _)
;

predicate ror_pub_pred_enc(int current, item pay, int k_info,
                           int server, int p1, int p2) =
  k_info == int_pair(0, server) &*&
  INT_MIN <= p1 && p1 <= INT_MAX &*&
  INT_MIN <= p2 && p2 <= INT_MAX &*&
  pay == pair_item(?key_gen,
           pair_item(data_item(chars_of_int(p1)),
             pair_item(data_item(chars_of_int(p2)), ?nonce))) &*&
  key_gen == symmetric_key_item(server, _) &*&
  info_for_item(key_gen) == int_pair(1, int_pair(p1, p2)) &*&
  nonce == nonce_item(current, _, 0) &*&
  p1 == current ?
    p2 == int_right(info_for_item(nonce))
  :
    p2 == current &*&
    p1 == int_left(info_for_item(nonce))
;

predicate ror_pub(item i) =
  col ? true :
  switch (i)
  {
    case data_item(d0):
      return true;
    case pair_item(f0, s0):
      return [_]ror_pub(f0) &*&
             [_]ror_pub(s0);
    case nonce_item(p0, c0, inc0):
      return true;
    case hash_item(pay0): return
      switch (pay0)
      {
        case some(pay1):
          return [_]ror_pub(pay1);
        case none:
          return true;
      };
    case symmetric_key_item(p0, c0):
      return true == ror_key_clsfy(p0, c0, true);
    case public_key_item(p0, c0):
      return true;
    case private_key_item(p0, c0):
      return true == ror_key_clsfy(p0, c0, false);
    case hmac_item(p0, c0, pay0): return
      switch(pay0)
      {
        case some(pay1):
          return ror_key_clsfy(p0, c0, true) ?
                   [_]ror_pub(pay1)
                 :
                   [_]ror_pub_pred_hmac(p0, pay1, 
                                        info_for_item(i), _, _, _);
        case none:
          return true;
      };
    case symmetric_encrypted_item(p0, c0, pay0, ent0): return
      switch(pay0)
      {
        case some(pay1):
          return ror_key_clsfy(p0, c0, true) ?
                   [_]ror_pub(pay1)
                 :
                   [_]ror_pub_pred_enc(p0, pay1, 
                                       info_for_item(i), _, _, _);
        case none:
          return true;
      };
    case asymmetric_encrypted_item(p0, c0, pay0, ent0): return
      switch (pay0)
      {
        case some(pay1): return
          [_]ror_pub(pay1);
        case none:
          return true;
      };
    case asymmetric_signature_item(p0, c0, pay0, ent0): return
      switch (pay0)
      {
        case some(pay1):
          return [_]ror_pub(pay1);
        case none:
          return true;
      };
  }
;

@*/

///////////////////////////////////////////////////////////////////////////////
// Implementation prototypes for this protocol ////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

struct keys{
  int principal;
  struct item *key;
  struct keys *next;
};

/*@
predicate keys(int server, struct keys* k) =
  k == 0 ?
    true
  :
    malloc_block_keys(k) &*&
    k->principal |-> ?principal &*&
    k->key |-> ?key &*& k->next |-> ?next &*&
    item(key, ?ikey, ror_pub) &*&
    ikey == symmetric_key_item(principal, _) &*&
    info_for_item(ikey) == int_pair(0, server) &*&
    keys(server, next)
;
@*/

struct keys * add_key(struct keys *keys, struct item *key, int principal);
  /*@ requires keys(?server, keys) &*& item(key, ?k, ror_pub) &*&
                 k == symmetric_key_item(principal, _) &*&
                 info_for_item(k) == int_pair(0, server); @*/
  //@ ensures  keys(server, result);

void remove_keys(struct keys *keys);
  //@ requires keys(?server, keys);
  //@ ensures  true;

struct item *lookup_key(struct keys *keys, int principal);
  //@ requires [?f]keys(?server, keys);
  /*@ ensures  [f]keys(server, keys) &*& item(result, ?k, ror_pub) &*&
                 k == symmetric_key_item(principal, _) &*&
                 info_for_item(k) == int_pair(0, server); @*/

int participant(bool initial, int server, int current, int next,
                int port_prev, int port_next, struct item *key,
                struct item **key1, struct item **key2);
  /*@ requires [?f0]world(ror_pub, ror_key_clsfy) &*& 
               principal(current, ?count) &*&
               item(key, ?k, ror_pub) &*&
                 info_for_item(k) == int_pair(0, server) &*&
                 k == symmetric_key_item(current, ?cc) &*&
               *key1 |-> _ &*& *key2 |-> _; @*/
  /*@ ensures  [f0]world(ror_pub, ror_key_clsfy) &*& 
               principal(current, count + 1) &*&
               item(key, k, ror_pub) &*&
               *key2 |-> ?p_key2 &*&
               item(p_key2, ?k2, ror_pub) &*&
               col || ror_key_clsfy(current, cc, true) ||
               info_for_item(k2) == int_pair(1, int_pair(current, next)) &*&
               initial ? *key1 |-> _ :
                 *key1 |-> ?p_key1 &*& item(p_key1, ?k1, ror_pub) &*&
                 col || ror_key_clsfy(current, cc, true) ||
                 info_for_item(k1) == 
                   int_pair(1, int_pair(result, current)); @*/

void server(int server, struct keys *k, int port);
  /*@ requires [?f0]world(ror_pub, ror_key_clsfy) &*& 
               principal(server, _) &*& keys(server, k); @*/
  /*@ ensures  [f0]world(ror_pub, ror_key_clsfy) &*& 
               principal(server, _) &*& keys(server, k); @*/

///////////////////////////////////////////////////////////////////////////////
// Attacker proof obligations for this protocol ///////////////////////////////
///////////////////////////////////////////////////////////////////////////////

//@ PROOFS_DEFAULT(ror)

#endif
