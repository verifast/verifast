#include "../include/cryptolib.h"

//To include some constants
#include "general.h"
//To start the polarssl attacker
#include "principals.h"
#include "../polarssl/annotated_api/polarssl.h"

void send_data(struct network_status *net_stat)
  /*@ requires [?f0]world(?pub) &*&
               proof_obligations(pub) &*&
               network_status(net_stat) &*&
               generated_values(?principal, ?count1); @*/
  /*@ ensures  [f0]world(pub) &*&
               proof_obligations(pub) &*&
               network_status(net_stat) &*&
               generated_values(principal, ?count2); @*/
{
  int data_size = random_int();
  if (data_size > POLARSSL_MIN_RANDOM_BYTE_SIZE)
  {
    char* data = malloc((int) data_size);
    if (data == 0) abort_crypto_lib("malloc failed");
    random_buffer(data, data_size);
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
  /*@ requires [?f0]world(?pub) &*&
               proof_obligations(pub) &*&
               network_status(net_stat) &*&
               generated_values(?principal, ?count1) &*&
               true == bad(principal); @*/
  /*@ ensures  [f0]world(pub) &*&
               proof_obligations(pub) &*&
               network_status(net_stat) &*&
               generated_values(principal, ?count2); @*/
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
  /*@ requires [?f0]world(?pub) &*&
               proof_obligations(pub) &*&
               network_status(net_stat) &*&
               generated_values(?principal, ?count1) &*&
               true == bad(principal); @*/
  /*@ ensures  [f0]world(pub) &*&
               proof_obligations(pub) &*&
               network_status(net_stat) &*&
               generated_values(principal, ?count2); @*/
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
    //@ if (collision_in_run()) proof2(f);
    //@ assert item(second, ?s, pub);
    //@ if (collision_in_run()) proof2(s);
    //@ close proof_obligations(pub);
    network_send(net_stat, first);
    network_send(net_stat, second);
    item_free(first);
    item_free(second);
  }
  item_free(pair);
}

void send_nonce(struct network_status *net_stat)
  /*@ requires [?f0]world(?pub) &*&
               proof_obligations(pub) &*&
               network_status(net_stat) &*&
               generated_values(?principal, ?count1) &*&
               true == bad(principal); @*/
  /*@ ensures  [f0]world(pub) &*&
               proof_obligations(pub) &*&
               network_status(net_stat) &*&
               generated_values(principal, ?count2); @*/
{
  int i = random_int();
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
  /*@ requires [?f0]world(?pub) &*&
               proof_obligations(pub) &*&
               network_status(net_stat) &*&
               generated_values(?principal, ?count1) &*&
               true == bad(principal); @*/
  /*@ ensures  [f0]world(pub) &*&
               proof_obligations(pub) &*&
               network_status(net_stat) &*&
               generated_values(principal, ?count2); @*/
{
  struct item *nonce = network_receive(net_stat);
  //@ assert item(nonce, ?n, pub);
  if (is_nonce(nonce))
  {
    increment_nonce(nonce);
    //@ assert item(nonce, ?n_inc, pub);
    //@ open proof_obligations(pub);
    /*@ if (collision_in_run())
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
  /*@ requires [?f0]world(?pub) &*&
               keypair(keypair, ?attacker_id, ?id, ?info, pub) &*&
               proof_obligations(pub) &*&
               network_status(net_stat) &*&
               generated_values(attacker_id, ?count1) &*&
               true == bad(attacker_id); @*/
  /*@ ensures  [f0]world(pub) &*&
               keypair(keypair, attacker_id, id, info, pub) &*&
               proof_obligations(pub) &*&
               network_status(net_stat) &*&
               generated_values(attacker_id, ?count2); @*/
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
  /*@ requires [?f0]world(?pub) &*&
               keypair(keypair, ?attacker_id, ?id, ?info, pub) &*&
               proof_obligations(pub) &*&
               network_status(net_stat) &*&
               generated_values(attacker_id, ?count1) &*&
               true == bad(attacker_id); @*/
  /*@ ensures  [f0]world(pub) &*&
               keypair(keypair, attacker_id, id, info, pub) &*&
               proof_obligations(pub) &*&
               network_status(net_stat) &*&
               generated_values(attacker_id, ?count2); @*/
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
    /*@ if (collision_in_run())
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
  /*@ requires [?f0]world(?pub) &*&
               keypair(keypair, ?attacker_id, ?id, ?info, pub) &*&
               proof_obligations(pub) &*&
               network_status(net_stat) &*&
               generated_values(attacker_id, ?count1) &*&
               true == bad(attacker_id); @*/
  /*@ ensures  [f0]world(pub) &*&
               keypair(keypair, attacker_id, id, info, pub) &*&
               proof_obligations(pub) &*&
               network_status(net_stat) &*&
               generated_values(attacker_id, ?count2); @*/
{
  struct item *key = network_receive(net_stat);
  //@ assert item(key, ?k, pub);
  if (is_symmetric_key(key))
  {
    struct item *pay = network_receive(net_stat);
    //@ assert item(pay, ?p, pub);
    struct item *enc = symmetric_encryption(key, pay);
    
    //@ assert item(enc, ?e, pub);
    //@ open proof_obligations(pub);
    /*@ if (collision_in_run())
        {
          assert is_public_collision(?proof, pub);
          proof(e);
        }
        else
        {
          assert is_public_symmetric_encrypted(?proof, pub);
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

void send_symmetric_decrypted(struct network_status *net_stat, struct keypair *keypair)
  /*@ requires [?f0]world(?pub) &*&
               keypair(keypair, ?attacker_id, ?id, ?info, pub) &*&
               proof_obligations(pub) &*&
               network_status(net_stat) &*&
               generated_values(attacker_id, ?count1) &*&
               true == bad(attacker_id); @*/
  /*@ ensures  [f0]world(pub) &*&
               keypair(keypair, attacker_id, id, info, pub) &*&
               proof_obligations(pub) &*&
               network_status(net_stat) &*&
               generated_values(attacker_id, ?count2); @*/
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
      /*@ if (collision_in_run())
          {
            assert is_public_collision(?proof, pub);
            proof(d);
          }
          else
          {
            assert is_public_symmetric_decrypted(?proof, pub);
            proof(e);
          }
      @*/
      network_send(net_stat, dec);
      
      struct item *enc2 = symmetric_encryption(key, dec);
      //@ assert item(enc2, ?e2, pub);
      /*@ if (collision_in_run())
          {
            assert is_public_collision(?proof, pub);
            proof(e2);
          }
          else
          {
            assert e2 == symmetric_encrypted_item(?p, ?c, ?pay, ?ent0);
            assert is_public_symmetric_encrypted_entropy(?proof, pub);
            proof(e, ent0);
          }
      @*/
      network_send(net_stat, enc2);
      //@ close proof_obligations(pub);
      
      item_free(dec);
      item_free(enc2);
    }
    item_free(enc);
  }
  item_free(key);
}


void send_asymmetric_encrypted(struct network_status *net_stat, struct keypair *keypair)
  /*@ requires [?f0]world(?pub) &*&
               keypair(keypair, ?attacker_id, ?id, ?info, pub) &*&
               proof_obligations(pub) &*&
               network_status(net_stat) &*&
               generated_values(attacker_id, ?count1) &*&
               true == bad(attacker_id); @*/
  /*@ ensures  [f0]world(pub) &*&
               keypair(keypair, attacker_id, id, info, pub) &*&
               proof_obligations(pub) &*&
               network_status(net_stat) &*&
               generated_values(attacker_id, ?count2); @*/
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
    /*@ if (collision_in_run())
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
  /*@ requires [?f0]world(?pub) &*&
               keypair(keypair, ?attacker_id, ?id, ?info, pub) &*&
               proof_obligations(pub) &*&
               network_status(net_stat) &*&
               generated_values(attacker_id, ?count1) &*&
               true == bad(attacker_id); @*/
  /*@ ensures  [f0]world(pub) &*&
               keypair(keypair, attacker_id, id, info, pub) &*&
               proof_obligations(pub) &*&
               network_status(net_stat) &*&
               generated_values(attacker_id, ?count2); @*/
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
      struct item *dec = asymmetric_decryption(key, enc);
      
      //@ assert item(dec, ?d, pub);
      //@ open proof_obligations(pub);
      /*@ if (collision_in_run())
          {
            assert is_public_collision(?proof, pub);
            proof(d);
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
    item_free(enc);
  }
  item_free(key);
}

void send_asymmetric_signature(struct network_status *net_stat, 
                               struct keypair *keypair)
  /*@ requires [?f0]world(?pub) &*&
               keypair(keypair, ?attacker_id, ?id, ?info, pub) &*&
               proof_obligations(pub) &*&
               network_status(net_stat) &*&
               generated_values(attacker_id, ?count1) &*&
               true == bad(attacker_id); @*/
  /*@ ensures  [f0]world(pub) &*&
               keypair(keypair, attacker_id, id, info, pub) &*&
               proof_obligations(pub) &*&
               network_status(net_stat) &*&
               generated_values(attacker_id, ?count2); @*/
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
    /*@ if (collision_in_run())
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
            
void attacker(int attacker_id, struct keypair* keypair)
  /*@ requires [?f]world(?pub) &*&
               true == bad(attacker_id) &*&
               generated_values(attacker_id, ?count) &*&
               keypair(keypair, attacker_id, ?id, ?info, pub) &*&
               principals_created(_); @*/
  //@ ensures false;
{
  for (;;)
    /*@ invariant [f]world(pub) &*&
                  generated_values(attacker_id, _) &*&
                  keypair(keypair, attacker_id, id, info, pub) &*&
                  principals_created(_); @*/
  {
    struct network_status *net_stat = 0;
    int net_choise = random_int();
    int port = random_int();
    if (net_choise % 2 == 0)
      net_stat = network_bind_and_accept(port % 65536);
    else
      net_stat = network_connect("localhost", port % 65536);

    {
      //@ retreive_proof_obligations();
      int action = random_int();

      int* c;
      switch (action % 13)
      {
        case 0:
          c = get_polarssl_principals();
          //@ open [f]world(pub);
          polarssl_attacker(c);
          //@ close [f]world(pub);
          //@ return_polarssl_principals();
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
      //@ leak proof_obligations(pub);
    }

    network_disconnect(net_stat);
  }
}
