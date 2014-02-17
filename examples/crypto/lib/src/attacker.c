#include "dolevyao.h"
#include "attacker.h"

void attacker()
  /*@ requires exists<fixpoint(item, bool)>(?pub) &*& 
               [?f0]world(pub) &*& [?f1]net_api_initialized() &*&
               attacker_proof_obligations(pub) &*&
               initial_principals();
  @*/
  //@ ensures false;
{
  //@ open initial_principals();
  for (;;)
    /*@ invariant [f0]world(pub) &*& [f1]net_api_initialized() &*&
                  attacker_proof_obligations(pub) &*& principals(_); 
    @*/
  {
    // Attackers are arbitrary principals.
    struct item* a_key_sym;
    struct keypair* a_key_pair;
    int bad_one = create_principal(&a_key_sym, &a_key_pair);
    struct item* a_key_pub = keypair_get_private_key(a_key_pair);
    struct item* a_key_pri = keypair_get_public_key(a_key_pair);
    
    struct network_status *net_stat = 0;
    int net_choise = choose();
    int port = choose();
    if (net_choise % 2 == 0)
      net_stat = network_bind(port % 65536);
    else
      net_stat = network_connect("localhost", port % 65536);
    
    for (;;)
      /*@ 
          invariant [f0]world(pub) &*& [f1]net_api_initialized() &*& 
                    attacker_proof_obligations(pub) &*& principals(_) &*&
                    generated_nonces(bad_one, 0) &*&
                    a_key_sym |-> ?key_sym &*&
                    key_item(key_sym, bad_one, 0, symmetric_key, int_pair(0, 0)); 
      @*/
    {
      //@ open attacker_proof_obligations(pub);
      int action = choose();
      
      int data;
      struct item *item;
      struct item *first;
      struct item *second;
      struct item *pair;
      struct item *key;
      struct item *hash;
      
      switch (action % 7) 
      {
        case 0:
          // Bad principals leak their server key...
          //@ assume(bad(bad_one));
          //@ open key_item(a_key_sym, bad_one, 0, symmetric_key, ?a_info);
          /*@ assert is_can_send_bad_principal_keys(
                                         ?can_send_bad_principal_keys, pub); @*/
          //@ can_send_bad_principal_keys(bad_one);
          network_send(net_stat, a_key_sym);
          //@ close key_item(a_key_sym, bad_one, 0, symmetric_key, a_info);
          break;
        case 1:
          // Anyone can publish arbitrary data items...
          data = choose();
          item = create_data_item(data);
          //@ assert is_can_send_data(?can_send_data, pub);
          //@ can_send_data(data);
          network_send(net_stat, item);
          item_free(item);
          break;
        case 2:
          // Anyone can create pairs of public items...
          first = network_receive_attempt(net_stat);
          second = network_receive_attempt(net_stat);
          if (first !=0 && second != 0)
          {
            pair = create_pair(first, second);
            //@ assert is_can_send_public_pair(?can_send_public_pair, pub);
            //@ can_send_public_pair();
            network_send(net_stat, pair);
            item_free(pair);
          }
          if (first != 0) item_free(first);
          if (second != 0) item_free(second);
          break;
        case 3:
          // Anyone can deconstruct a public pair...
          pair = network_receive_attempt(net_stat);
          if (pair != 0)
          {
            first = pair_get_first(pair);
            second = pair_get_second(pair);
            /*@ assert is_can_send_decomposed_public_pair(
                                      ?can_send_decomposed_public_pair, pub); @*/
            //@ can_send_decomposed_public_pair();
            network_send(net_stat, first);
            network_send(net_stat, second);
            item_free(first);
            item_free(second);
            item_free(pair);
          }
          break;
        case 4:
          // Anyone can encrypt a public item with a published key...
          key = network_receive_attempt(net_stat);
          if (key != 0)
          {
            first = network_receive_attempt(net_stat);
            if (first != 0)
            {
              check_is_key(key);
              second = encrypt(key, first);
              //@ open key_item(key, _, _, _, _);
              /*@ assert is_can_send_public_encrypted(
                                              ?can_send_public_encrypted, pub); @*/
              //@ can_send_public_encrypted();
              network_send(net_stat, second);
              item_free(first);
              item_free(second);
            }
            item_free(key);
          }
          break;
        case 5:
          // Anyone can decrypt a public item with a published key...
          key = network_receive_attempt(net_stat);
          if (key != 0)
          {
            first = network_receive_attempt(net_stat);
            if (first != 0)
            {
              check_is_key(key);
              second = decrypt(key, first);
              //@ open key_item(key, ?foo, ?bar, ?baz, ?baq);
              /*@ assert is_can_send_public_decrypted(
                                              ?can_send_public_decrypted, pub); @*/
              //@ can_send_public_decrypted();
              network_send(net_stat, second);
              item_free(first);
              item_free(second);
            }
            item_free(key);
          }
          break;
        case 6:
          key = network_receive_attempt(net_stat);
          if (key != 0)
          {
            item = network_receive_attempt(net_stat);
            if (item != 0)
            {
              check_is_key(key);
              hash = hmac(key, item);
              //@ open key_item(key, _, _, _, _);
              /*@ assert is_can_send_public_hmac(
                                              ?can_send_public_hmac, pub); @*/
              //@ can_send_public_hmac();
              network_send(net_stat, hash);
              item_free(item);
              item_free(hash);
            }
            item_free(key);
          }
          break;
      }
      //@ close attacker_proof_obligations(_);
    }
    break;
  }
}

