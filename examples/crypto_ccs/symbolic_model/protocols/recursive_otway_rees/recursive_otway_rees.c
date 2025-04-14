#include "recursive_otway_rees.h"

#include <stdlib.h>
#include <stdio.h>

#define VERIFY_EXTRA
#define VERIFY_PRINCIPAL_1
#define VERIFY_PRINCIPAL_2
#define VERIFY_PRINCIPAL
#define VERIFY_SERVER_1
#define VERIFY_SERVER_2
#define VERIFY_SERVER

/*@
#define CLOSE_PUB(I) \
  { \
    close ror_pub(I); \
    leak ror_pub(I); \
  }
@*/

struct item *get_int(int data)
  //@ requires [?f0]world(ror_pub, ror_key_clsfy);
  /*@ ensures  [f0]world(ror_pub, ror_key_clsfy) &*&
               item(result, ?d, ror_pub) &*&
               d == data_item(chars_of_int(data)) &*&
               [_]ror_pub(d); @*/
{
  return create_data_item_from_int(data);
  //@ assert item(_, ?d, ror_pub);
  //@ CLOSE_PUB(d)
}

#ifdef VERIFY_EXTRA
struct keys *add_key(struct keys *keys, struct item *key, int principal)
  /*@ requires keys(?server, keys) &*& item(key, ?k, ror_pub) &*&
                 k == symmetric_key_item(principal, _) &*&
                 info_for_item(k) == int_pair(0, server); @*/
  //@ ensures  keys(server, result);
{
  struct keys *result = malloc(sizeof(struct keys));
  if (result == 0) abort_crypto_lib("Malloc failed");
  result->principal = principal;
  result->key = key;
  result->next = keys;
  //@ close keys(server, result);
  return result;
}

void remove_keys(struct keys *keys)
  //@ requires keys(?server, keys);
  //@ ensures  true;
{
  //@ open keys(server, keys);
  if (keys != 0)
  {
    remove_keys(keys->next);
    item_free(keys->key);
    free(keys);
  }
}

struct item *lookup_key(struct keys *keys, int principal)
  //@ requires [?f]keys(?server, keys);
  /*@ ensures  [f]keys(server, keys) &*& item(result, ?k, ror_pub) &*&
                 k == symmetric_key_item(principal, _) &*&
                 info_for_item(k) == int_pair(0, server); @*/
{
  //@ open [f]keys(server, keys);
  if (keys == 0)
    abort_crypto_lib("Key not found");

  if (keys->principal == principal)
  {
    return item_clone(keys->key);
    //@ close [f]keys(server, keys);
  }
  else
  {
    return lookup_key(keys->next, principal);
    //@ close [f]keys(server, keys);
  }
}
#endif

#ifdef VERIFY_PRINCIPAL_1
struct item *participant_construct(int server, int prev, int current, int next,
                                   struct item *nonce, struct item *key,
                                   struct item* msg_prev)
  /*@ requires [?f0]world(ror_pub, ror_key_clsfy) &*&
               [?f1]item(nonce, ?n, ror_pub) &*& [_]ror_pub(n) &*&
                 info_for_item(n) == int_pair(prev, next) &*&
                 n == nonce_item(current, ?c1, 0) &*&
               [?f2]item(key, ?k, ror_pub) &*&
                 info_for_item(k) == int_pair(0, server) &*&
                 k == symmetric_key_item(current, ?c2) &*&
               item(msg_prev, ?m, ror_pub) &*& [_]ror_pub(m) &*&
                 m == data_item(chars_of_int(INITIAL_MSG)) ?
                   prev == INITIAL_MSG
                 :
                   col ? true :
                   m == pair_item(
                          pair_item(data_item(chars_of_int(prev)),
                            pair_item(data_item(chars_of_int(current)), _)), _); @*/
  /*@ ensures  [f0]world(ror_pub, ror_key_clsfy) &*&
               [f1]item(nonce, n, ror_pub) &*& [f2]item(key, k, ror_pub) &*&
               item(result, ?r, ror_pub) &*& [_]ror_pub(r); @*/
{
  struct item *p1 = get_int(current);
  //@ assert item(p1, ?d_p1, ror_pub);
  struct item *p2 = get_int(next);
  //@ assert item(p2, ?d_p2, ror_pub);

  struct item *m1 = create_pair(nonce, msg_prev);
  //@ assert item(m1, ?p_m1, ror_pub);
  //@ assert p_m1 == pair_item(n, m);
  //@ CLOSE_PUB(p_m1)
  struct item *m2 = create_pair(p2, m1);
  //@ assert item(m2, ?p_m2, ror_pub);
  //@ assert p_m2 == pair_item(d_p2, p_m1);
  //@ CLOSE_PUB(p_m2)
  struct item *m3 = create_pair(p1, m2);
  //@ assert item(m3, ?p_m3, ror_pub);
  //@ assert p_m3 == pair_item(d_p1, p_m2);
  //@ CLOSE_PUB(p_m3)
  struct item *hmac = create_hmac(key, m3);

  //@ assert item(hmac, ?h, ror_pub);
  /*@ if (!col)
      {
        assert h == hmac_item(current, ?c3, some(p_m3));
        if (!ror_key_clsfy(current, c3, true))
        {
          close ror_pub_pred_hmac(current, p_m3,
                  info_for_item(h), server, prev, next);
          leak  ror_pub_pred_hmac(current, p_m3,
                  info_for_item(h), server, prev, next);
        }
      }
  @*/
  //@ close ror_pub(h);
  //@ leak ror_pub(h);
  struct item *result = create_pair(m3 , hmac);
  //@ assert item(result, ?r, ror_pub);
  //@ CLOSE_PUB(r)
  item_free(p1); item_free(p2); item_free(hmac);
  item_free(m1); item_free(m2); item_free(m3);
  item_free(msg_prev);

  return result;
}
#endif

#ifdef VERIFY_PRINCIPAL_2
struct item *participant_process(int server, int previous, int current, int next,
                                 bool up, struct item *msg, struct item *nonce,
                                 struct item *key)
  /*@ requires [?f0]world(ror_pub, ror_key_clsfy) &*&
               principal(current, ?count) &*&
               item(msg, ?m, ror_pub) &*& [_]ror_pub(m) &*&
               item(nonce, ?n, ror_pub) &*&
                 info_for_item(n) == int_pair(previous, next) &*&
                 n == nonce_item(current, _, 0) &*&
               item(key, ?k, ror_pub) &*&
                 info_for_item(k) == int_pair(0, server) &*&
                 k == symmetric_key_item(current, ?cc); @*/
  /*@ ensures  [f0]world(ror_pub, ror_key_clsfy) &*&
               principal(current, count) &*&
               item(nonce, n, ror_pub) &*& item(key, k, ror_pub) &*&
               item(result, ?r, ror_pub) &*&
               up ?
                 col || ror_key_clsfy(current, cc, true) ||
                 info_for_item(r) ==
                   int_pair(1, int_pair(current, next))
               :
                 col || ror_key_clsfy(current, cc, true) ||
                 info_for_item(r) ==
                   int_pair(1, int_pair(previous, current)); @*/
{
  struct item *result;

  check_is_symmetric_encrypted(msg);
  struct item *dec = symmetric_decryption(key, msg);
  //@ assert item(dec, ?dec_i, ror_pub);

  result = pair_get_first(dec);
  //@ assert item(result, ?r, ror_pub);
  struct item *temp1 = pair_get_second(dec);
  //@ assert item(temp1, ?t1, ror_pub);
  //@ assert col || dec_i == pair_item(r, t1);

  struct item *d1    = pair_get_first(temp1);
  //@ assert item(d1, ?d1_i, ror_pub);
  check_is_data(d1);
  struct item *temp2 = pair_get_second(temp1);
  //@ assert item(temp2, ?t2, ror_pub);
  //@ assert col || t1 == pair_item(d1_i, t2);

  struct item *d2    = pair_get_first(temp2);
  //@ assert item(d2, ?d2_i, ror_pub);
  check_is_data(d2);
  struct item *n2     = pair_get_second(temp2);
  //@ assert item(n2, ?n2_i, ror_pub);
  //@ assert col || t2 == pair_item(d2_i, n2_i);

  item_check_equal(nonce, n2);
  int p1 = item_get_data_as_int(d1);
  int p2 = item_get_data_as_int(d2);
  if (up)
  {
    if (p1 != current)
      abort_crypto_lib("Participant received corrupt message 1");
    if (p2 != next)
      abort_crypto_lib("Participant received corrupt message 2");
  }
  else
  {
    if (p1 != previous)
      abort_crypto_lib("Participant received corrupt message 3");
    if (p2 != current)
      abort_crypto_lib("Participant received corrupt message 4");
  }

  item_free(dec); item_free(msg);
  item_free(d1); item_free(d2); item_free(n2);
  item_free(temp1); item_free(temp2);

  /*@ if (!col)
      {
        open [_]ror_pub(m);
        if (!ror_key_clsfy(current, cc, true))
        {
          open ror_pub_pred_enc(?current2, ?pay2, ?k_info2,
                                ?server2, ?p1_2, ?p2_2);
          assert r == symmetric_key_item(server , _);
          int_of_chars_of_int(p1_2);
          int_of_chars_of_int(p2_2);
          assert info_for_item(r) ==
                   int_pair(1, int_pair(p1, p2));
        }
      }
  @*/
  return result;
}
#endif

#ifdef VERIFY_PRINCIPAL
int participant(bool initial, int server, int current, int next,
                int port_prev, int port_next, struct item *key,
                struct item **key1, struct item **key2)
  /*@ requires [?f0]world(ror_pub, ror_key_clsfy) &*&
               principal(current, ?count) &*&
               item(key, ?k, ror_pub) &*&
                 info_for_item(k) == int_pair(0, server) &*&
                 k == symmetric_key_item(current, ?c1) &*&
               *key1 |-> _ &*& *key2 |-> _; @*/
  /*@ ensures  [f0]world(ror_pub, ror_key_clsfy) &*&
               principal(current, count + 1) &*&
               item(key, k, ror_pub) &*&
               *key2 |-> ?p_key2 &*&
               item(p_key2, ?k2, ror_pub) &*&
               col || ror_key_clsfy(current, c1, true) ||
               info_for_item(k2) ==
                 int_pair(1, int_pair(current, next)) &*&
               initial ? *key1 |-> _  :
                 *key1 |-> ?p_key1 &*& item(p_key1, ?k1, ror_pub) &*&
                 col || ror_key_clsfy(current, c1, true) ||
                 info_for_item(k1) ==
                   int_pair(1, int_pair(result, current)); @*/
{
  struct network_status *net_stat_prev;
  if (!initial) net_stat_prev = network_bind_and_accept(port_prev);
  struct network_status *net_stat_next =
    network_connect("localhost", port_next);

  // Receiving from previous participant
  int prev;
  struct item *msg_prev;
  if (initial)
  {
    prev = INITIAL_MSG;
    msg_prev = get_int(INITIAL_MSG);
  }
  else
  {
    msg_prev = network_receive(net_stat_prev);
    struct item *temp1 = pair_get_first(msg_prev);
    check_is_pair(temp1);
    struct item *temp2 = pair_get_first(temp1);
    check_is_data(temp2);
    prev = item_get_data_as_int(temp2);
    struct item *temp3 = pair_get_second(temp1);
    struct item *temp4 = pair_get_first(temp3);
    check_is_data(temp4);
    if (item_get_data_as_int(temp4) != current)
      abort_crypto_lib("Participant received message out of chain");
    item_free(temp1); item_free(temp2);
    item_free(temp3); item_free(temp4);
  }

  //@ assert item(msg_prev, ?i_msg_prev, ror_pub);
  // Generate nonce for this session
  //@ close nonce_request(current, int_pair(prev, next));
  struct item *nonce = create_nonce();
  //@ assert item(nonce, ?n_nonce, ror_pub);
  //@ close ror_pub(n_nonce);
  //@ leak ror_pub(n_nonce);

  // Forward the message to next participant
  struct item *msg = participant_construct(server, prev, current, next,
                                           nonce, key, msg_prev);
  network_send(net_stat_next, msg);
  item_free(msg);

  // Receiving from next participant
  msg = network_receive(net_stat_next);
  //@ assert item(msg, ?msg_i, ror_pub);
  struct item *msg1;
  struct item *msg2;
  if (initial)
  {
    check_is_symmetric_encrypted(msg);
    msg2 = msg;
  }
  else
  {
    check_is_pair(msg);
    msg2 = pair_get_first(msg);
    //@ assert item(msg2, ?m2_i, ror_pub);
    struct item *m = pair_get_second(msg);
    //@ assert item(m, ?m_i, ror_pub);
    msg1 = pair_get_first(m);
    //@ assert item(msg1, ?m1_i, ror_pub);
    struct item *rest = pair_get_second(m);
    //@ assert item(rest, ?rest_i, ror_pub);
    /*@ if (!col)
        {
          open [_]ror_pub(msg_i); open [_]ror_pub(m_i);
        }
        else
        {
          close ror_pub(m1_i); leak ror_pub(m1_i);
          close ror_pub(m2_i); leak ror_pub(m2_i);
          close ror_pub(rest_i); leak ror_pub(rest_i);
        }
    @*/
    network_send(net_stat_prev, rest);
    item_free(rest); item_free(m);
    item_free(msg);
  }
  struct item *temp;
  temp = participant_process(server, prev, current, next,
                             true, msg2, nonce, key);
  *key2 = temp;
  if (!initial)
  {
    temp = participant_process(server, prev, current, next,
                               false, msg1, nonce, key);
    *key1 = temp;
  }

  item_free(nonce);
  if (!initial) network_disconnect(net_stat_prev);
  network_disconnect(net_stat_next);

  return prev;
}
#endif

struct processed_messages{
  int p1; int p2; int p3;
  struct item *n2;
  struct item *k2;
  struct item *k12;
  struct item *k23;
  struct processed_messages *next;
};

/*@
predicate processed_messages(struct processed_messages* m, int server,
                             int previous, int current, int next) =
  INT_MIN <= previous && previous <= INT_MAX &*&
  INT_MIN <= current && current <= INT_MAX &*&
  INT_MIN <= next && next <= INT_MAX &*&
  m == 0 ?
    true
  :
    malloc_block_processed_messages(m) &*&
    m->p1 |-> previous &*& m->p2 |-> current &*& m->p3 |-> next &*&
    previous != current && current != next && previous != next &*&
    m->n2  |-> ?n2 &*& m->k2 |-> ?k2 &*&
    m->k12  |-> ?k12  &*& m->k23 |-> ?k23 &*&
    m->next |-> ?next_pm &*&
      processed_messages(next_pm, server, _, ?previous2, ?current2) &*&
      item(k2, ?ki, ror_pub) &*&
      ki == symmetric_key_item(current, ?c2) &*&
      info_for_item(ki) == int_pair(0, server) &*&
      item(n2, ?ni, ror_pub) &*&
      ni == nonce_item(?p_n, ?c_n, ?inc_n) &*& [_]ror_pub(ni) &*&
      col || ror_key_clsfy(current, c2, true) ||
        (p_n == current && inc_n == 0 &&
         info_for_item(ni) == int_pair(previous2, next)
        ) &*&
      item(k23, ?k23i, ror_pub) &*&
      k23i == symmetric_key_item(server, ?c23) &*&
      info_for_item(k23i) == int_pair(1, int_pair(current, next)) &*&
      (col || ror_key_clsfy(server, c23, true) ? [_]ror_pub(k23i) : true) &*&
      next_pm == 0 ?
        previous == INITIAL_MSG
      :
        previous == previous2 && current == current2 &*&
        item(k12, ?k12i, ror_pub) &*&
        k12i == symmetric_key_item(server, ?c12) &*&
        info_for_item(k12i) == int_pair(1, int_pair(previous, current)) &*&
        (col || ror_key_clsfy(server, c12, true) ? [_]ror_pub(k12i) : true)
;
@*/

#ifdef VERIFY_SERVER_1
struct processed_messages *server_process(struct keys *keys, struct item *msg)
  /*@ requires [?f0]world(ror_pub, ror_key_clsfy) &*&
               principal(?server, ?count) &*& keys(server, keys) &*&
               item(msg, ?msg_i, ror_pub) &*& [_]ror_pub(msg_i); @*/
  /*@ ensures  [f0]world(ror_pub, ror_key_clsfy) &*&
               principal(server, _) &*& keys(server, keys) &*&
               processed_messages(result, server, ?previous, ?current, ?next) &*&
               col || result == 0  ? true :
                 msg_i == pair_item(pair_item(data_item(chars_of_int(current)),
                                    pair_item(data_item(chars_of_int(next)), _)), _); @*/
{
  struct processed_messages *result = 0;

  if (is_data(msg))
  {
    if (item_get_data_as_int(msg) != INITIAL_MSG)
      abort_crypto_lib("Server got mallformed message");
    item_free(msg);
    //@ close processed_messages(result, server, 0, 0, 0);
    return 0;
  }
  else
  {
    result = calloc(1, sizeof(struct processed_messages));
    if (result == 0) abort_crypto_lib("Malloc failed");

    //@ open [_]ror_pub(msg_i);
    check_is_pair(msg);
    struct item *temp1 = pair_get_first(msg);
    //@ assert item(temp1, ?m1_i, ror_pub);
    struct item *hmac = pair_get_second(msg);
    //@ assert item(hmac, ?hmac_i, ror_pub);
    //@ assert col || msg_i == pair_item(m1_i, hmac_i);
    check_is_pair(temp1);
    struct item *p2_ = pair_get_first(temp1);
    check_is_data(p2_);
    result->p2 = item_get_data_as_int(p2_);
    //@ assert result->p2 |-> ?p2_val;
    //@ assert item(p2_, ?d_p2, ror_pub);
    //@ assert col || d_p2 == data_item(chars_of_int(p2_val));
    result->k2 = lookup_key(keys, result->p2);
    //@ assert result->k2 |-> ?k2;
    //@ assert item(k2, ?k2i, ror_pub);
    //@ assert k2i == symmetric_key_item(p2_val, ?c2);
    //@ if (col) {close ror_pub(m1_i); leak ror_pub(m1_i);}
    struct item *hmac2 = create_hmac(result->k2, temp1);
    item_check_equal(hmac, hmac2);
    item_free(hmac2);
    struct item *temp2 = pair_get_second(temp1);
    //@ assert item(temp2, ?m2_i, ror_pub);
    //@ assert col || m1_i == pair_item(d_p2, m2_i);
    struct item *p3_ = pair_get_first(temp2);
    check_is_data(p3_);
    result->p3 = item_get_data_as_int(p3_);
    //@ assert result->p3 |-> ?p3_val;
    //@ assert item(p3_, ?d_p3, ror_pub);
    //@ assert col || d_p3 == data_item(chars_of_int(p3_val));
    struct item *temp3 = pair_get_second(temp2);
    //@ assert item(temp3, ?m3_i, ror_pub);
    //@ assert col || m2_i == pair_item(d_p3, m3_i);
    result->n2 = pair_get_first(temp3);
    check_is_nonce(result->n2);
    //@ assert result->n2 |-> ?n2;
    //@ assert item(n2, ?n2i, ror_pub);
    struct item *rest = pair_get_second(temp3);
    //@ assert item(rest, ?ri, ror_pub);
    //@ assert col || m3_i == pair_item(n2i, ri);
    /*@ if (!col)
        {
          assert hmac_i == hmac_item(p2_val, c2, some(m1_i));
          open [_]ror_pub(hmac_i);
          open [_]ror_pub(m1_i); open [_]ror_pub(m2_i); open [_]ror_pub(m3_i);
          if (!ror_key_clsfy(p2_val, c2, true))
          {
            open [_]ror_pub_pred_hmac(p2_val, m1_i, info_for_item(hmac_i),
                                      ?server2, ?p1_val2, ?p3_val2);
            assert server == server2;
            int_of_chars_of_int(p3_val2);
            assert p3_val == p3_val2;
            assert info_for_item(n2i) == int_pair(p1_val2, p3_val2);
          }
        }
        else
        {
          close ror_pub(n2i); leak ror_pub(n2i);
          close ror_pub(ri); leak ror_pub(ri);
        }
    @*/

    //@ int info = int_pair(1, int_pair(p2_val, p3_val));
    //@ close key_request(server, info);
    result->k23 = create_symmetric_key();
    //@ assert result->k23 |-> ?key &*& item(key, ?k, ror_pub);
    //@ assert k == symmetric_key_item(server, ?c23);
    /*@ if (col || ror_key_clsfy(server, c23, true))
        {
          close ror_pub(k);
          leak ror_pub(k);
        }
    @*/
    result->next = server_process(keys, rest);
    //@ open processed_messages(result->next, server, ?p1_n, ?p2_n, ?p3_n);
    if (result->next == 0)
    {
      result->p1 = INITIAL_MSG;
    }
    else
    {
      if (result->p2 != result->next->p3)
        abort_crypto_lib("Server received corrupted chained message 1");
      result->p1 = result->next->p2;
      //@ assert p2_val == p3_n;
      result->k12 = item_clone(result->next->k23);
    }
    if (result->p1 == result->p2 || result->p2 == result->p3 || result->p1 == result->p3)
        abort_crypto_lib("Server received corrupted chained message 2");
    //@ close processed_messages(result->next, server, p1_n, p2_n, p3_n);
    //@ assert result->next |-> ?next &*& result->p1 |-> ?p1;
    /*@ if (!col)
        {
          if (!ror_key_clsfy(p2_val, c2, true))
          {
            assert n2i == nonce_item(p2_val, _, 0);
            assert [_]ror_pub_pred_hmac(p2_val, m1_i, info_for_item(k2i),
                                        ?server2, ?p1_val2, ?p3_val2);
            assert info_for_item(n2i) == int_pair(p1_val2, p3_val2);
            assert next == 0  ? true :
                ri == pair_item(pair_item(data_item(chars_of_int(p2_n)),
                                pair_item(data_item(chars_of_int(p3_n)), _)), _);
            int_of_chars_of_int(p3_val2);
            assert p3_val == p3_val2;

            int_of_chars_of_int(p2_n);
            int_of_chars_of_int(p1_val2);

            if (next == 0)
            {
              assert p1 == INITIAL_MSG;
              open processed_messages(result->next, server, p1_n, p2_n, p3_n);
              close processed_messages(result->next, server, 0, p1_val2, p3_val2);
            }
            else
            {
              assert p1 == p1_val2;
            }
          }
        }
    @*/
    item_free(temp1); item_free(temp2); item_free(temp3);
    item_free(hmac); item_free(p2_); item_free(p3_); item_free(msg);
    //@ close processed_messages(result, server, p1, p2_val, p3_val);
    return result;
  }
}
#endif

#ifdef VERIFY_SERVER_2
struct item *server_serialize(struct processed_messages *msgs)
  /*@ requires [?f0]world(ror_pub, ror_key_clsfy) &*&
               principal(?server, ?s_id) &*&
               processed_messages(msgs, server, _, _, _) &*& msgs != 0; @*/
  /*@ ensures  [f0]world(ror_pub, ror_key_clsfy) &*&
               principal(server, _) &*&
               item(result, ?r, ror_pub) &*& [_]ror_pub(r); @*/
{
  //@ open processed_messages(msgs, server, _, _, _);
  //@ assert msgs->p1 |-> ?p1 &*& msgs->p2 |-> ?p2 &*& msgs->p3 |-> ?p3;
  //@ assert msgs->k2 |-> ?k2 &*& item(k2, ?k2i, ror_pub);
  //@ assert k2i == symmetric_key_item(?s2, ?c2);
  //@ assert msgs->n2 |-> ?n2 &*& item(n2, ?n2i, ror_pub);
  //@ assert msgs->next |-> ?next;

  struct item *result = 0;
  {
    struct item *d2 = get_int(msgs->p2);
    //@ assert item(d2, ?d2i, ror_pub) &*& d2i == data_item(chars_of_int(p2));
    struct item *d3 = get_int(msgs->p3);
    //@ assert item(d3, ?d3i, ror_pub) &*& d3i == data_item(chars_of_int(p3));
    struct item *m1 = create_pair(d3, msgs->n2);
    //@ assert item(m1, ?m1i, ror_pub);
    //@ assert m1i == pair_item(d3i, n2i);
    //@ CLOSE_PUB(m1i)
    struct item *m2 = create_pair(d2, m1);
    //@ assert item(m2, ?m2i, ror_pub);
    //@ assert m2i == pair_item(d2i, m1i);
    //@ CLOSE_PUB(m2i)
    struct item *m3 = create_pair(msgs->k23, m2);
    //@ assert item(m3, ?m3i, ror_pub);
    //@ item n = nonce_item(server, s_id + 1, 0);
    //@ close ror_pub(n);
    //@ leak  ror_pub(n);
    result = symmetric_encryption(msgs->k2, m3);
    //@ assert item(result, ?r, ror_pub);
    //@ assert msgs->k23 |-> ?k23 &*& item(k23, ?k23i, ror_pub);

    /*@ if (col || ror_key_clsfy(s2, c2, true))
        {
          CLOSE_PUB(m3i)
        }
        else
        {
          assert r == symmetric_encrypted_item(p2, _, some(m3i), _);
          assert m3i == pair_item(k23i, m2i);
          assert m2i == pair_item(data_item(chars_of_int(p2)), m1i);
          assert m1i == pair_item(data_item(chars_of_int(p3)), n2i);
          close ror_pub_pred_enc(p2, m3i, info_for_item(k2i), server, p2, p3);
          leak ror_pub_pred_enc(p2, m3i, info_for_item(k2i), server, p2, p3);
        }
    @*/
    //@ close ror_pub(r);
    //@ leak ror_pub(r);
    item_free(m1); item_free(m2); item_free(m3);
    item_free(d2); item_free(d3); item_free(msgs->k23);
  }
  //@ assert item(result, ?r1, ror_pub) &*& [_]ror_pub(r1);

  if (msgs->next != 0)
  {
    struct item *result2 = 0;
    struct item *result3 = 0;
    struct item *d1 = get_int(msgs->p1);
    //@ assert item(d1, ?d1i, ror_pub) &*& d1i == data_item(chars_of_int(p1));
    struct item *d2 = get_int(msgs->p2);
    //@ assert item(d2, ?d2i, ror_pub) &*& d2i == data_item(chars_of_int(p2));
    struct item *m1 = create_pair(d2, msgs->n2);
    //@ assert item(m1, ?m1i, ror_pub);
    //@ assert m1i == pair_item(d2i, n2i);
    //@ CLOSE_PUB(m1i)
    struct item *m2 = create_pair(d1, m1);
    //@ assert item(m2, ?m2i, ror_pub);
    //@ assert m2i == pair_item(d1i, m1i);
    //@ CLOSE_PUB(m2i)
    struct item *m3 = create_pair(msgs->k12, m2);
    //@ assert item(m3, ?m3i, ror_pub);
    //@ item n = nonce_item(server, s_id + 3, 0);
    //@ close ror_pub(n);
    //@ leak  ror_pub(n);
    result2 = symmetric_encryption(msgs->k2, m3);
    //@ assert item(result2, ?r, ror_pub);
    //@ assert msgs->k12 |-> ?k12 &*& item(k12, ?k12i, ror_pub);

    /*@ if (col || ror_key_clsfy(s2, c2, true))
        {
          CLOSE_PUB(m3i)
        }
        else
        {
          assert r == symmetric_encrypted_item(p2, _, some(m3i), _);
          assert m3i == pair_item(k12i, m2i);
          assert m2i == pair_item(data_item(chars_of_int(p1)), m1i);
          assert m1i == pair_item(data_item(chars_of_int(p2)), n2i);
          close ror_pub_pred_enc(p2, m3i, info_for_item(k2i), server, p1, p2);
          leak ror_pub_pred_enc(p2, m3i, info_for_item(k2i), server, p1, p2);
        }
    @*/
    //@ close ror_pub(r);
    //@ leak ror_pub(r);
    item_free(m1); item_free(m2); item_free(m3);
    item_free(d1); item_free(d2); item_free(msgs->k12);

    result3 = server_serialize(msgs->next);
    //@ assert item(result2, ?r2, ror_pub) &*& [_]ror_pub(r2);
    //@ assert item(result3, ?r3, ror_pub) &*& [_]ror_pub(r3);
    struct item* temp1 = create_pair(result2, result3);
    //@ assert item(temp1, ?t1, ror_pub);
    //@ CLOSE_PUB(t1)
    struct item* temp2 = create_pair(result, temp1);
    //@ assert item(temp2, ?t2, ror_pub);
    //@ CLOSE_PUB(t2)
    item_free(result); item_free(result2);
    item_free(result3); item_free(temp1);
    result = temp2;
  }
  //@ if (next == 0) open processed_messages(0, _, _, _, _);
  //@ assert item(result, ?r2, ror_pub) &*& [_]ror_pub(r2);
  item_free(msgs->n2); item_free(msgs->k2);
  free(msgs);
  //@ assert item(result, ?r, ror_pub) &*& [_]ror_pub(r);
  return result;
}
#endif

#ifdef VERIFY_SERVER
void server(int server, struct keys *keys, int port)
  /*@ requires [?f0]world(ror_pub, ror_key_clsfy) &*& 
               principal(server, _) &*& keys(server, keys); @*/
  /*@ ensures  [f0]world(ror_pub, ror_key_clsfy) &*& 
               principal(server, _) &*& keys(server, keys); @*/
{
  struct network_status *net_stat = network_bind_and_accept(port);
  struct item *msg = network_receive(net_stat);
  struct processed_messages *msgs = server_process(keys, msg);
  //@ open processed_messages(msgs, server, ?p1, ?p2, ?p3);
  if (msgs == 0)
        abort_crypto_lib("Message was to short");
  if (msgs->p3 != server)
        abort_crypto_lib("Message was not intended for this server");
  //@ close processed_messages(msgs, server, p1, p2, p3);
  struct item *result = server_serialize(msgs);
  network_send(net_stat, result);
  item_free(result);

  network_disconnect(net_stat);
}
#endif
