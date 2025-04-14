#include "../include/symbolic.h"

//To include some constants
#include "general.h"
//To start the polarssl attacker
#include "principal_ids.h"
#include "../../annotated_api/mbedTLS_definitions.h"

void random_buffer_(char* buffer, int size)
  /*@ requires [?f]world(?pub, ?key_clsfy) &*&
               proof_obligations(pub) &*&
               chars_(buffer, size, _) &*&
               principal(?principal, ?count) &*&
               true == bad(principal); @*/
  /*@ ensures  [f]world(pub, key_clsfy) &*&
               proof_obligations(pub) &*&
               chars(buffer, size, _) &*&
               principal(principal, count + 1); @*/
{
  //@ open proof_obligations(pub);
  //@ assert is_public_nonce(?proof, _);
  //@ proof(nonce_item(principal, count + 1, 0));
  random_buffer(buffer, size);
  //@ close proof_obligations(pub);
}

int random_int_()
  /*@ requires [?f]world(?pub, ?key_clsfy) &*&
               proof_obligations(pub) &*&
               principal(?principal, ?count) &*&
               true == bad(principal); @*/
  /*@ ensures  [f]world(pub, key_clsfy) &*&
               proof_obligations(pub) &*&
               principal(principal, count + 1); @*/
{
  //@ open proof_obligations(pub);
  //@ assert is_public_nonce(?proof, _);
  //@ proof(nonce_item(principal, count + 1, 0));
  return random_int();
  //@ close proof_obligations(pub);
}

void send_data(struct network_status *net_stat)
  /*@ requires [?f0]world(?pub, ?key_clsfy) &*&
               proof_obligations(pub) &*&
               network_status(net_stat) &*&
               principal(?principal, ?count1) &*&
               true == bad(principal); @*/
  /*@ ensures  [f0]world(pub, key_clsfy) &*&
               proof_obligations(pub) &*&
               network_status(net_stat) &*&
               principal(principal, ?count2); @*/
{
  int data_size = random_int_();
  if (data_size > MIN_RANDOM_SIZE)
  {
    char* data = malloc((size_t)data_size);
    if (data == 0) abort_crypto_lib("malloc failed");
    random_buffer_(data, data_size);
    struct item *item = create_data_item(data, data_size);
    //@ assert item(item, ?i, pub) &*& i == data_item(?d);
    free(data);
    //@ open proof_obligations(pub);
    //@ assert is_public_data(?proof, pub);
    //@ proof(i);
    //@ close proof_obligations(pub);
    network_send(net_stat, item);
    item_free(item);
  }
}

void send_pair_composed(struct network_status *net_stat)
  /*@ requires [?f0]world(?pub, ?key_clsfy) &*&
               proof_obligations(pub) &*&
               network_status(net_stat) &*&
               principal(?principal, ?count1) &*&
               true == bad(principal); @*/
  /*@ ensures  [f0]world(pub, key_clsfy) &*&
               proof_obligations(pub) &*&
               network_status(net_stat) &*&
               principal(principal, ?count2); @*/
{
  struct item *first = network_receive(net_stat);
  struct item *second = network_receive(net_stat);
  struct item * pair = create_pair(first, second);
  //@ assert item(first, ?f, pub);
  //@ assert item(second, ?s, pub);
  //@ assert item(pair, pair_item(f, s), pub);

  //@ open proof_obligations(pub);
  //@ assert is_public_pair_compose(?proof, pub);
  //@ proof(f, s);
  //@ close proof_obligations(pub);
  network_send(net_stat, pair);
  item_free(pair);
  item_free(first);
  item_free(second);
}

void send_pair_decomposed(struct network_status *net_stat)
  /*@ requires [?f0]world(?pub, ?key_clsfy) &*&
               proof_obligations(pub) &*&
               network_status(net_stat) &*&
               principal(?principal, ?count1) &*&
               true == bad(principal); @*/
  /*@ ensures  [f0]world(pub, key_clsfy) &*&
               proof_obligations(pub) &*&
               network_status(net_stat) &*&
               principal(principal, ?count2); @*/
{
  struct item *pair = network_receive(net_stat);
  //@ assert item(pair, ?p, pub);
  if (is_pair(pair))
  {
    struct item *first = pair_get_first(pair);
    struct item *second = pair_get_second(pair);
    //@ open proof_obligations(pub);
    //@ assert is_public_pair_decompose(?proof1, pub);
    //@ assert is_public_collision(?proof2, pub);
    //@ proof1(p);
    //@ assert item(first, ?f, pub);
    //@ if (col) proof2(f);
    //@ assert item(second, ?s, pub);
    //@ if (col) proof2(s);
    //@ close proof_obligations(pub);
    network_send(net_stat, first);
    network_send(net_stat, second);
    item_free(first);
    item_free(second);
  }
  item_free(pair);
}

void send_nonce(struct network_status *net_stat)
  /*@ requires [?f0]world(?pub, ?key_clsfy) &*&
               proof_obligations(pub) &*&
               network_status(net_stat) &*&
               principal(?principal, ?count1) &*&
               true == bad(principal); @*/
  /*@ ensures  [f0]world(pub, key_clsfy) &*&
               proof_obligations(pub) &*&
               network_status(net_stat) &*&
               principal(principal, ?count2); @*/
{
  int i = random_int_();
  //@ close nonce_request(principal, i);
  struct item *nonce = create_nonce();
  //@ assert item(nonce, ?n, pub);
  //@ open proof_obligations(pub);
  //@ assert is_public_nonce(?proof, pub);
  //@ close exists(info_for_item);
  //@ proof(n);
  //@ close proof_obligations(pub);
  network_send(net_stat, nonce);
  item_free(nonce);
}

void increment_and_send_nonce(struct network_status *net_stat)
  /*@ requires [?f0]world(?pub, ?key_clsfy) &*&
               proof_obligations(pub) &*&
               network_status(net_stat) &*&
               principal(?principal, ?count1) &*&
               true == bad(principal); @*/
  /*@ ensures  [f0]world(pub, key_clsfy) &*&
               proof_obligations(pub) &*&
               network_status(net_stat) &*&
               principal(principal, ?count2); @*/
{
  struct item *nonce = network_receive(net_stat);
  //@ assert item(nonce, ?n, pub);
  if (is_nonce(nonce))
  {
    increment_nonce(nonce);
    //@ assert item(nonce, ?n_inc, pub);
    //@ open proof_obligations(pub);
    /*@ if (col)
        {
          assert is_public_collision(?proof, pub);
          proof(n_inc);
        }
        else
        {
          assert is_public_incremented_nonce(?proof, pub);
          proof(n, n_inc);
        }
    @*/
    //@ close proof_obligations(pub);
    network_send(net_stat, nonce);
  }
  item_free(nonce);
}

void send_keys(struct network_status *net_stat, struct keypair *keypair)
  /*@ requires [?f0]world(?pub, ?key_clsfy) &*&
               keypair(keypair, ?attacker_id, ?id, ?info, pub) &*&
               proof_obligations(pub) &*&
               network_status(net_stat) &*&
               principal(attacker_id, ?count1) &*&
               true == bad(attacker_id); @*/
  /*@ ensures  [f0]world(pub, key_clsfy) &*&
               keypair(keypair, attacker_id, id, info, pub) &*&
               proof_obligations(pub) &*&
               network_status(net_stat) &*&
               principal(attacker_id, ?count2); @*/
{
  //@ close key_request(attacker_id, 0);
  struct item *key_sym = create_symmetric_key();
  struct item *key_priv = keypair_get_private_key(keypair);
  struct item *key_pub = keypair_get_public_key(keypair);
  //@ assert item(key_sym, ?k_sym, pub);
  //@ assert item(key_pub, ?k_pub, pub);
  //@ assert item(key_priv, ?k_priv, pub);
  //@ open proof_obligations(pub);
  //@ assert is_public_symmetric_key(?proof_sym, pub);
  //@ assert is_public_public_key(?proof_pub, pub);
  //@ assert is_public_private_key(?proof_priv, pub);
  //@ proof_sym(k_sym);
  //@ proof_pub(k_pub);
  //@ proof_priv(k_priv);
  //@ close proof_obligations(pub);
  network_send(net_stat, key_sym);
  network_send(net_stat, key_pub);
  network_send(net_stat, key_priv);
  item_free(key_sym);
  item_free(key_pub);
  item_free(key_priv);
}

void send_hmac(struct network_status *net_stat, struct keypair *keypair)
  /*@ requires [?f0]world(?pub, ?key_clsfy) &*&
               keypair(keypair, ?attacker_id, ?id, ?info, pub) &*&
               proof_obligations(pub) &*&
               network_status(net_stat) &*&
               principal(attacker_id, ?count1) &*&
               true == bad(attacker_id); @*/
  /*@ ensures  [f0]world(pub, key_clsfy) &*&
               keypair(keypair, attacker_id, id, info, pub) &*&
               proof_obligations(pub) &*&
               network_status(net_stat) &*&
               principal(attacker_id, ?count2); @*/
{
  struct item *key = network_receive(net_stat);
  //@ assert item(key, ?k, pub);
  if (is_symmetric_key(key))
  {
    struct item *pay = network_receive(net_stat);
    //@ assert item(pay, ?p, pub);
    struct item *mac = create_hmac(key, pay);

    //@ assert item(mac, ?h, pub);
    //@ open proof_obligations(pub);
    /*@ if (col)
        {
          assert is_public_collision(?proof, pub);
          proof(h);
        }
        else
        {
          assert is_public_hmac(?proof, pub);
          proof(h);
        }
    @*/
    //@ close proof_obligations(pub);
    network_send(net_stat, mac);

    item_free(mac);
    item_free(pay);
  }
  item_free(key);
}

void send_symmetric_encrypted(struct network_status *net_stat, struct keypair *keypair)
  /*@ requires [?f0]world(?pub, ?key_clsfy) &*&
               keypair(keypair, ?attacker_id, ?id, ?info, pub) &*&
               proof_obligations(pub) &*&
               network_status(net_stat) &*&
               principal(attacker_id, ?count1) &*&
               true == bad(attacker_id); @*/
  /*@ ensures  [f0]world(pub, key_clsfy) &*&
               keypair(keypair, attacker_id, id, info, pub) &*&
               proof_obligations(pub) &*&
               network_status(net_stat) &*&
               principal(attacker_id, ?count2); @*/
{
  struct item *key = network_receive(net_stat);
  //@ assert item(key, ?k, pub);
  if (is_symmetric_key(key))
  {
    struct item *pay = network_receive(net_stat);
    //@ assert item(pay, ?p, pub);
    
    //@ open proof_obligations(pub);
    //@ item nonce = nonce_item(attacker_id, count1 + 1, 0);
    //@ assert is_public_nonce(?proof1, pub);
    //@ proof1(nonce);
    struct item *enc = symmetric_encryption(key, pay);
    //@ assert item(enc, ?e, pub);
    /*@ if (col)
        {
          assert is_public_collision(?proof2, pub);
          proof2(e);
        }
        else
        {
          assert is_public_symmetric_encrypted(?proof2, pub);
          proof2(e);
        }
    @*/
    //@ close proof_obligations(pub);
    network_send(net_stat, enc);

    item_free(enc);
    item_free(pay);
  }
  item_free(key);
}

void send_symmetric_decrypted(struct network_status *net_stat, struct keypair *keypair)
  /*@ requires [?f0]world(?pub, ?key_clsfy) &*&
               keypair(keypair, ?attacker_id, ?id, ?info, pub) &*&
               proof_obligations(pub) &*&
               network_status(net_stat) &*&
               principal(attacker_id, ?count1) &*&
               true == bad(attacker_id); @*/
  /*@ ensures  [f0]world(pub, key_clsfy) &*&
               keypair(keypair, attacker_id, id, info, pub) &*&
               proof_obligations(pub) &*&
               network_status(net_stat) &*&
               principal(attacker_id, ?count2); @*/
{
  struct item *key = network_receive(net_stat);
  //@ assert item(key, ?k, pub);
  if (is_symmetric_key(key))
  {
    struct item *enc = network_receive(net_stat);
    //@ assert item(enc, ?e, pub);
    if (is_symmetric_encrypted(enc))
    {
      struct item *dec = symmetric_decryption(key, enc);
      //@ assert item(dec, ?d, pub);
      //@ open proof_obligations(pub);
      /*@ if (!col)
          {
            assert is_public_symmetric_decrypted(?proof, pub);
            proof(e);
          }
      @*/
      network_send(net_stat, dec);
      //@ close proof_obligations(pub);
      item_free(dec);
    }
    item_free(enc);
  }
  item_free(key);
}

void send_asymmetric_encrypted(struct network_status *net_stat, struct keypair *keypair)
  /*@ requires [?f0]world(?pub, ?key_clsfy) &*&
               keypair(keypair, ?attacker_id, ?id, ?info, pub) &*&
               proof_obligations(pub) &*&
               network_status(net_stat) &*&
               principal(attacker_id, ?count1) &*&
               true == bad(attacker_id); @*/
  /*@ ensures  [f0]world(pub, key_clsfy) &*&
               keypair(keypair, attacker_id, id, info, pub) &*&
               proof_obligations(pub) &*&
               network_status(net_stat) &*&
               principal(attacker_id, ?count2); @*/
{
  struct item *key = network_receive(net_stat);
  //@ assert item(key, ?k, pub);
  if (is_public_key(key))
  {
    struct item *pay = network_receive(net_stat);
    //@ assert item(pay, ?p, pub);
    struct item *enc = asymmetric_encryption(key, pay);

    //@ assert item(enc, ?e, pub);
    //@ open proof_obligations(pub);
    /*@ if (col)
        {
          assert is_public_collision(?proof, pub);
          proof(e);
        }
        else
        {
          assert is_public_asymmetric_encrypted(?proof, pub);
          proof(e);
        }
    @*/
    //@ close proof_obligations(pub);
    network_send(net_stat, enc);

    item_free(enc);
    item_free(pay);
  }
  item_free(key);
}

void send_asymmetric_decrypted(struct network_status *net_stat, struct keypair *keypair)
  /*@ requires [?f0]world(?pub, ?key_clsfy) &*&
               keypair(keypair, ?attacker_id, ?id, ?info, pub) &*&
               proof_obligations(pub) &*&
               network_status(net_stat) &*&
               principal(attacker_id, ?count1) &*&
               true == bad(attacker_id); @*/
  /*@ ensures  [f0]world(pub, key_clsfy) &*&
               keypair(keypair, attacker_id, id, info, pub) &*&
               proof_obligations(pub) &*&
               network_status(net_stat) &*&
               principal(attacker_id, ?count2); @*/
{
  struct item *key = network_receive(net_stat);
  //@ assert item(key, ?k, pub);
  if (is_private_key(key))
  {
    //@ assert k == private_key_item(?principal2, ?count2);
    struct item *enc = network_receive(net_stat);
    //@ assert item(enc, ?e, pub);
    if (is_asymmetric_encrypted(enc))
    {
      //@ assert e == asymmetric_encrypted_item(?principal3, ?count3, ?pay, ?ent);
      char tag;
      //@ close chars_(&tag, 1, _);
      random_buffer_(&tag, 1);
      //@ open chars(&tag, 1, _);
      if (tag == TAG_DATA || tag == TAG_PAIR ||           
          tag == TAG_NONCE || tag == TAG_HASH ||          
          tag == TAG_SYMMETRIC_KEY || tag == TAG_PUBLIC_KEY ||   
          tag == TAG_PRIVATE_KEY || tag == TAG_HMAC ||    
          tag == TAG_SYMMETRIC_ENC || tag == TAG_ASYMMETRIC_ENC ||  
          tag == TAG_ASYMMETRIC_SIG)
      {
        struct item *dec = asymmetric_decryption(key, enc, tag);
        //@ assert item(dec, ?d, pub);
        //@ open proof_obligations(pub);
        /*@ if (col)
            {
              assert [_]pub(d);
            }
            else if (principal2 == principal3 && count2 == count3)
            {
              assert pay == some(d);
              assert is_public_asymmetric_decrypted(?proof, pub);
              proof(e);
            }
            else
            {
              assert [_]pub(d);
            }
        @*/
        network_send(net_stat, dec);
        //@ close proof_obligations(pub);
        item_free(dec);
      }
    }
    item_free(enc);
  }
  item_free(key);
}

void send_asymmetric_signature(struct network_status *net_stat,
                               struct keypair *keypair)
  /*@ requires [?f0]world(?pub, ?key_clsfy) &*&
               keypair(keypair, ?attacker_id, ?id, ?info, pub) &*&
               proof_obligations(pub) &*&
               network_status(net_stat) &*&
               principal(attacker_id, ?count1) &*&
               true == bad(attacker_id); @*/
  /*@ ensures  [f0]world(pub, key_clsfy) &*&
               keypair(keypair, attacker_id, id, info, pub) &*&
               proof_obligations(pub) &*&
               network_status(net_stat) &*&
               principal(attacker_id, ?count2); @*/
{
  struct item *key = network_receive(net_stat);
  //@ assert item(key, ?k, pub);
  if (is_private_key(key))
  {
    struct item *pay = network_receive(net_stat);
    //@ assert item(pay, ?p, pub);
    struct item *sig = asymmetric_signature(key, pay);

    //@ assert item(sig, ?s, pub);
    //@ open proof_obligations(pub);
    /*@ if (col)
        {
          assert is_public_collision(?proof, pub);
          proof(s);
        }
        else
        {
          assert is_public_asymmetric_signature(?proof, pub);
          proof(s);
        }
    @*/
    //@ close proof_obligations(pub);
    network_send(net_stat, sig);

    item_free(sig);
    item_free(pay);
  }
  item_free(key);
}

void symbolic_attacker(int attacker_id, struct keypair* keypair)
  /*@ requires [?f]world(?pub, ?key_clsfy) &*&
               true == bad(attacker_id) &*&
               principal(attacker_id, ?count) &*&
               keypair(keypair, attacker_id, ?id, ?info, pub); @*/
  //@ ensures false;
{
  //@ retreive_proof_obligations();

  for (;;)
    /*@ invariant [f]world(pub, key_clsfy) &*&
                  proof_obligations(pub) &*&
                  principal(attacker_id, _) &*&
                  keypair(keypair, attacker_id, id, info, pub); @*/
  {
    struct network_status *net_stat = 0;
    int net_choise = random_int_();
    int port = random_int_();
    if (net_choise % 2 == 0)
      net_stat = network_bind_and_accept(port % 65536);
    else
      net_stat = network_connect("localhost", port % 65536);

    {
      int action = random_int_();
      int *counter;
      switch (action % 13)
      {
        case 0:
          //@ open [f]world(pub, key_clsfy);
          //@ assert [_]is_key_classifier(_, pub, key_clsfy);
          //@ retreive_public_invariant_constraints(key_clsfy);
          //@ duplicate_lemma_function_pointer_chunk(key_classifier);
          /*@ {
                lemma void public_key_classifier(cryptogram key, int p, int c,
                                                bool symmetric)
                  requires polarssl_proof_pred(pub, key_clsfy)() &*&
                          [_]polarssl_pub(pub)(key) &*&
                          symmetric ?
                            key == cg_symmetric_key(p, c)
                          :
                            key == cg_rsa_private_key(p, c);
                  ensures polarssl_proof_pred(pub, key_clsfy)() &*&
                          col || true == key_clsfy(p, c, symmetric);
                {
                  open [_]polarssl_pub(pub)(key);
                  item k;
                  if (symmetric)
                    k = symmetric_key_item(p, c);
                  else
                    k = private_key_item(p, c);
                  
                  open polarssl_proof_pred(pub, key_clsfy)();
                  assert is_key_classifier(?proof, pub, key_clsfy);
                  proof(k, p, c, symmetric);
                  close polarssl_proof_pred(pub, key_clsfy)();
                }
                produce_lemma_function_pointer_chunk(public_key_classifier) :
                  public_key_classifier(polarssl_pub(pub), key_clsfy,
                                        polarssl_proof_pred(pub, key_clsfy))
                                        (key__, p__, c__, sym__)
                  { call(); }
                  {duplicate_lemma_function_pointer_chunk(public_key_classifier);};
              }
          @*/
          //@ close polarssl_proof_pred(pub, key_clsfy)();
          attacker();
          //@ open polarssl_proof_pred(pub, key_clsfy)();
          //@ close [f]world(pub, key_clsfy);
          //@ leak public_invariant_constraints(_, _);
          //@ leak is_public_key_classifier(_, _, _, _);
          //@ leak is_key_classifier(_, _, _);
          break;
        case 1:
          // Anyone can publish arbitrary data items...
          send_data(net_stat);
          break;
        case 2:
          // Anyone can create pairs of public items...
          send_pair_composed(net_stat);
          break;
        case 3:
         // Anyone can deconstruct a public pair...
          send_pair_decomposed(net_stat);
          break;
        case 4:
          // Bad principals can publish generated nonce items...
          send_nonce(net_stat);
          break;
        case 5:
          // Bad principals can increment public nonces...
          increment_and_send_nonce(net_stat);
          break;
        case 6:
          // Bad principals can leak their keys...
          send_keys(net_stat, keypair);
          break;
        case 7:
          // Anyone can hmac public payload with public key
          send_hmac(net_stat, keypair);
          break;
        case 8:
          // Anyone can symmteric encrypt public payload with public key
          send_symmetric_encrypted(net_stat, keypair);
          break;
        case 9:
          // Anyone can symmteric decrypt message with public key
          send_symmetric_decrypted(net_stat, keypair);
          break;
        case 10:
          // Anyone can asymmteric encrypt public payload with public key
          send_asymmetric_encrypted(net_stat, keypair);
          break;
        case 11:
          // Anyone can asymmteric decrypt message with public key
          send_asymmetric_decrypted(net_stat, keypair);
          break;
        case 12:
          // Anyone can asymmteric sign public payload with public key
          send_asymmetric_signature(net_stat, keypair);
      }
    }
    network_disconnect(net_stat);
  }
}
