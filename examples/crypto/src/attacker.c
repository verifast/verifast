#include "attacker.h"

#include "item.h"

void attacker()
  /*@ requires exists<fixpoint(item, bool)>(?pub) &*&
               [?f0]world(pub) &*&
               attacker_proof_obligations(pub) &*&
               principals_created(_); @*/
  //@ ensures false;
{
  for (;;)
    /*@ invariant [f0]world(pub) &*&
                  attacker_proof_obligations(pub) &*& principals_created(_);
    @*/
  {
    // Attackers are arbitrary principals that are bad.
    int bad_one = create_principal();
    //@ close key_request(bad_one, int_pair(0,0));
    struct item* a_key_sym = create_symmetric_key();
    //@ assert item(a_key_sym, ?akey);
    //@ assert akey == key_item(bad_one, ?a_count, symmetric_key, ?a_info);
    //@ assume(bad(bad_one));
    
    struct network_status *net_stat = 0;
    int net_choise = random_int();
    int port = random_int();
    if (net_choise % 2 == 0)
      net_stat = network_bind_and_accept(port % 65536);
    else
      net_stat = network_connect("localhost", port % 65536);
    
    for (;;)
      /*@
          invariant [f0]world(pub) &*& network_status(net_stat) &*&
                    attacker_proof_obligations(pub) &*& 
                    principals_created(_) &*& item(a_key_sym, akey) &*&
                    generated_values(bad_one, _);
      @*/
    {
      //@ open attacker_proof_obligations(pub);
      int action = random_int();

      int data;
      struct item *item;
      struct item *first;
      struct item *second;
      struct item *pair;
      struct item *key;
      struct item *nonce;
      struct item *nonce_inc;
      struct item *hmaci;

      switch (action % 7)
      {
        case 0:
          // Bad principals leak their server key...
          /*@ assert is_can_send_bad_principal_keys(
                                         ?can_send_bad_principal_keys, pub); @*/
          //@ can_send_bad_principal_keys(bad_one);
          network_send(net_stat, a_key_sym);
          break;
        case 1:
          // Anyone can publish arbitrary data items...
          data = random_int();
          item = create_data_item(data);
          //@ assert is_can_send_data(?can_send_data, pub);
          //@ can_send_data(data);
          network_send(net_stat, item);
          item_free(item);
          break;
        case 2:
          // Anyone can create pairs of public items...
          first = network_receive(net_stat);
          second = network_receive(net_stat);
          
          pair = create_pair(first, second);
          //@ assert is_can_send_public_pair(?can_send_public_pair, pub);
          //@ assert item(first, ?fi) &*& item(second, ?si);
          //@ can_send_public_pair(first, second);
          network_send(net_stat, pair);
          item_free(pair);
          item_free(first);
          item_free(second);
          break;
        case 3:
          // Anyone can deconstruct a public pair...
          pair = network_receive(net_stat);
          
          first = pair_get_first(pair);
          second = pair_get_second(pair);
          /*@ assert is_can_send_decomposed_public_pair(
                                    ?can_send_decomposed_public_pair, pub); @*/
          //@ can_send_decomposed_public_pair(pair);
          network_send(net_stat, first);
          network_send(net_stat, second);
          item_free(pair);
          item_free(first);
          item_free(second);
          break;
        case 4:
          // Bad principals can send all generated nonces ...
          //@ close nonce_request(bad_one, int_pair(0, 0));
          nonce = create_nonce();
          check_is_nonce(nonce);
          /*@ assert is_can_send_bad_principal_nonce(
                                       ?can_send_bad_principal_nonce, pub); @*/
          //@ can_send_bad_principal_nonce(nonce);
          network_send(net_stat, nonce);
          item_free(nonce);
          break;
        case 5:
          // Anyone can send an incremented public nonce ...
          nonce = network_receive(net_stat);
          check_is_nonce(nonce);
          nonce_inc = item_clone(nonce); 
          increment_nonce(nonce_inc);
          //@ assert is_can_send_incremented_nonce(?can_send_inc_nonce, pub);
          //@ can_send_inc_nonce(nonce);
          network_send(net_stat, nonce);
          item_free(nonce);
          item_free(nonce_inc);
          break;
        case 6:
          // Anyone can hmac with public stuff ...
          key = network_receive(net_stat);
          item = network_receive(net_stat);
          check_is_key(key);
          hmaci = hmac(key, item);
          //@ assert is_can_send_public_hmac(?can_send_public_hmac, pub);
          //@ can_send_public_hmac(key, item, hmaci);
          network_send(net_stat, hmaci);
          item_free(item);
          item_free(hmaci);
          item_free(key);
          break;
        case 7:
          // Anyone can encrypt a public item with a published key...
          key = network_receive(net_stat);
          first = network_receive(net_stat);
          check_is_key(key);
          second = encrypt(key, first);
          /*@ assert is_can_send_public_encrypted(
                                          ?can_send_public_encrypted, pub); @*/
          //@ assert item(first, ?fff);
          //@ assert true == if_no_collision(pub(fff) == true);
          //@ can_send_public_encrypted(key, first, second);
          network_send(net_stat, second);
          item_free(key);
          item_free(first);
          item_free(second);
          break;
        case 8:
          // Anyone can decrypt a public item with a published key...
          key = network_receive(net_stat);
          first = network_receive(net_stat);
          check_is_key(key);
          check_is_encrypted(first);
          second = decrypt(key, first);
          /*@ assert is_can_send_public_decrypted(
                                          ?can_send_public_decrypted, pub); @*/
          //@ can_send_public_decrypted(key, second, first);
          network_send(net_stat, second);
          item_free(first);
          item_free(second);
          item_free(key);
          break;
      }
      //@ close attacker_proof_obligations(_);
    }
    break;
  }
}
