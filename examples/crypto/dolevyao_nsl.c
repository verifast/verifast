// See explanations in lib/dolevyao.h
#include "lib/dolevyao.h"
#include "stdlib.h"

/*

Dolev-Yao security verification of the Needham-Schroeder-Lowe public key 
authentication protocol

1. A -> B. {A,NA}_K(B)
2. B -> A. {B,NA,NB}_K(A)
3. A -> B. {NB}_K(B)

Goal: Secrets NA and NB shared between A and B

Client: A
Server: B

*/

///////////////////////////////////////////////////////////////////////////////
// Configuration for this protocol ////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

/*@ 
lemma void create_principal();
  requires principals(?count);
  ensures principals(count + 1) &*& generated_keys(count, 0);
@*/

/* 
info:
  int_pair(0, 0): for encryption
  int_pair(1, server): client nonce
  int_pair(2, int_pair(client, 
                int_pair(client_nonce_creator, 
                  int_pair(client_nonce_public_key, 
                    client_nonce_info)))): server nonce
*/

///////////////////////////////////////////////////////////////////////////////
// Definition of pub for this protocol ////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

/*@

// A definition of "pub" for the example protocol.
fixpoint bool mypub(item i) 
{
  switch (i) 
  {
    case pair_item(first0, second0):
      // For concatenation (Concatenations of public items are public)
      return mypub(first0) && mypub(second0);
    case data_item(d0): 
      // A & B
      return true;
    case key_item(p0, count0, kind0, info0): return
      // NA & NB (Both should remain secret)
      kind0 == public_key || bad(p0) || 
      int_left(info0) == 1 && bad(int_right(info0)) || 
      int_left(info0) == 2 && bad(int_left(int_right(info0)));
    case encrypted_item(p0, id0, kind0, info0, payload0, entropy0): return
      mypub(payload0) ||
      kind0 == public_key &&
      switch (payload0) 
      {
        // A -> B. {NB}_K(B)
        case key_item(creator1, id1, kind1, info1): return
          int_left(info1) == 2 && p0 == creator1 && 
          kind1 == private_key && info0 == int_pair(0, 0) &&
          int_left(int_right(info1)) == int_left(int_right(int_right(info1))) &&
          int_left(int_right(int_right(int_right(info1)))) == 0 &&
          int_right(int_right(int_right(int_right(info1)))) == int_pair(1, p0);
        case pair_item(first1, second2): return
          switch (second2) 
          {
            // A -> B. {A,NA}_K(B)
            case key_item(p3, id3, kind3, info3): return
              info3 == int_pair(1, p0) && first1 == data_item(p3) && 
              kind3 == private_key && info0 == int_pair(0, 0);
            // B -> A. {B,NA,NB}_K(A)
            case pair_item(first3, second3): return
              switch (second3) 
              {
                case key_item(p4, id4, kind4, info4): return
                  int_left(info4) == 2 && p0 == int_left(int_right(info4)) && 
                  kind4 == private_key && first1 == data_item(p4) && 
                  info0 == int_pair(0, 0) &&
                  (mypub(first3) ||
                   switch (first3) 
                   {
                     case key_item(p5, id5, kind5, info5): return
                       p5 == int_left(int_right(int_right(info4))) && p5 == p0 &&
                       (kind5 == public_key ? 1 : 0) == 
                         int_left(int_right(int_right(int_right(info4)))) &&
                       info5 == 
                         int_right(int_right(int_right(int_right(info4)))) &&
                       kind5 == private_key && info5 == int_pair(1, p4);
                     default: return false;
                   });
                default: return false;
              };
            default: return false;
          };
        default: return false;
      };
    default: return false;
  }
}

///////////////////////////////////////////////////////////////////////////////
// Protocol implementation ////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

@*/

void client(int client, int server, struct item *KA_PRIVATE, struct item *KB)
  /*@ requires generated_keys(client, _) &*& 
               world(mypub) &*& !bad(client) &*& !bad(server) &*&
               key_item(KA_PRIVATE, client, ?cskid, private_key, int_pair(0, 0)) &*&
               key_item(KB, server, ?spkid, public_key, int_pair(0, 0));
  @*/
  /*@ ensures  generated_keys(client, _) &*&
               world(mypub) &*&
               key_item(KA_PRIVATE, client, cskid, private_key, int_pair(0, 0)) &*&
               key_item(KB, server, spkid, public_key, int_pair(0, 0));
  @*/
{
  //1. A -> B. {A,NA}_K(B)
  struct item *NA = 0;
  {
    //@ close keypair_request(int_pair(1, server));
    struct keypair *noncePair = create_keypair();
    NA = keypair_get_private_key(noncePair);
    //@ open key_item(NA, _, _, _, _);
    struct item *i0 = keypair_get_public_key(noncePair);
    //@ open key_item(i0, _, _, _, _);
    item_free(i0);
    
    struct item *i1 = create_data_item(client); // A
    struct item *i2 = create_pair(i1, NA); // (A, NA)
    struct item *i3 = encrypt(KB, i2); // {(A, NA)}_K(B)
    net_send(i3);
    item_free(i1);
    item_free(i2);
    item_free(i3);
  }
   
  // 2. B -> A. {B,NA,NB}_K(A)
  struct item *NB = 0;
  {
    struct item *i4 = net_receive();
    struct item *i5 = decrypt(KA_PRIVATE, i4);
    struct item *i6 = pair_get_first(i5);
    int s = item_get_data(i6);
    if (s != server) abort();
    struct item *i7 = pair_get_second(i5);
    struct item *i8 = pair_get_first(i7);
    bool eq = item_equals(NA, i8);
    if (!eq) abort();
    NB = pair_get_second(i7);
    item_free(i4);
    item_free(i5);
    item_free(i6);
    item_free(i7);
    item_free(i8);
  }
    
  // 3. A -> B. {NB}_K(B)
  {
    //@ SWITCH_CRYPTO_PRIMITIVES(NB, 1, 1);
    struct item *i9 = encrypt(KB, NB);
    net_send(i9);
    item_free(i9);
  }
  
  //Protocol End Goals
  ///////////////////////////////////////////////////////////////////////////
  //1) Secrecy of NA
  //@ assert item(NA, ?cn);
  //@ assert !mypub(cn);
  //
  //2) Secrecy of NB
  //@ assert item(NB, ?sn);
  //@ assert !mypub(sn);
  //
  //3) Secrecy of KA_PRIVATE
  //@ assert !mypub(key_item(client, cskid, private_key, int_pair(0, 0)));
  ///////////////////////////////////////////////////////////////////////////
    
  item_free(NA);
  item_free(NB);
}

void server(int server, struct item *KB_PRIVATE)
  /*@ requires generated_keys(server, _) &*&
               world(mypub) &*& !bad(server) &*&
               key_item(KB_PRIVATE, server, ?sskid, private_key, int_pair(0, 0)); 
  @*/
  //@ ensures false;
{
  for (;;)
    /*@ invariant generated_keys(server, _) &*&
                  world(mypub) &*& !bad(server) &*&
                  key_item(KB_PRIVATE, server, sskid, private_key, int_pair(0, 0)); 
    @*/
  {
    // 1. A -> B. {A,NA}_K(B)
    int client = 0;
    struct item *NA = 0;
    {
      struct item *i1 = net_receive();
      struct item *i2 = decrypt(KB_PRIVATE, i1);
      struct item *i3 = pair_get_first(i2);
      client = item_get_data(i3);
      NA = pair_get_second(i2);
      check_is_key(NA);
      item_free(i1);
      item_free(i2);
      item_free(i3);
    }
    
    // 2. B -> A. {B,NA,NB}_K(A)
    //@ open key_item(NA, ?NACreator, ?NAId, ?NAIsPublicKey, ?NAInfo);
    struct item *NB = 0;
    {
      //@ assert item(NA, ?cn);
      //@ close public_key_request(int_pair(0, 0));
      struct item *KA = get_client_public_key(client);
      /*@ close keypair_request(
                  int_pair(2, 
                    int_pair(client, 
                      int_pair(NACreator, 
                        int_pair(NAIsPublicKey == 
                          public_key ? 1 : 0, NAInfo))))); @*/
      struct keypair *noncePair = create_keypair();
      NB = keypair_get_private_key(noncePair);
      //@ open key_item(NB, _, _, _, _);
      struct item *i0 = keypair_get_public_key(noncePair);
      //@ open key_item(i0, _, _, _, _);
      struct item *i1 = create_data_item(server);
      struct item *i2 = create_pair(NA, NB);
      struct item *i3 = create_pair(i1, i2);
      struct item *i4 = encrypt(KA, i3);
      net_send(i4);
      item_free(i0);
      item_free(i1);
      item_free(i2);
      item_free(i3);
      item_free(i4);
      //@ open key_item(KA, _, _, _, _);
      item_free(KA);
    }
      
    // 3. A -> B. {NB}_K(B)
    {
      struct item *i1 = net_receive();
      struct item *i2 = decrypt(KB_PRIVATE, i1);
      bool eq = item_equals(i2, NB);
      if (!eq) abort();
      item_free(i1);
      item_free(i2);
    }
    
    //Protocol End Goals
    ///////////////////////////////////////////////////////////////////////////
    //1) Secrecy of NA
    //@ assert item(NA, ?nc);
    //@ assert bad(client) || !mypub(nc);
    //
    //2) Secrecy of NB
    //@ assert item(NB, ?ns);
    //@ assert bad(client) || !mypub(ns);
    //
    //3) Secrecy of KB_PRIVATE
    //@ assert !mypub(key_item(server, sskid, private_key, int_pair(0, 0)));
    ///////////////////////////////////////////////////////////////////////////
  
    item_free(NA);
    item_free(NB);
  }
}

void attacker()
  //@ requires world(mypub) &*& principals(0);
  //@ ensures false;
{
  for (;;)
    //@ invariant world(mypub) &*& principals(?principalCount);
  {
    //@ create_principal(); // Attackers are arbitrary principals.
    for (;;)
      /*@ invariant world(mypub) &*& principals(_) &*& 
                    generated_keys(?me, ?keyCount); @*/
    {
      int action = choose();
      switch (action) 
      {
        case 0:
          // Bad principals leak private keys...
          int info = choose();
          //@ close keypair_request(info);
          struct keypair *keypair = create_keypair();
          struct item *sk = keypair_get_private_key(keypair);
          struct item *pk = keypair_get_public_key(keypair);
          //@ open key_item(sk, _, _, _, _);
          //@ open key_item(pk, _, _, _, _);
          net_send(pk);
          //@ assume(bad(me));
          net_send(sk);
          item_free(sk);
          item_free(pk);
          break;
        case 1:
          // Anyone can publish arbitrary data items...
          int data = choose();
          struct item *item = create_data_item(data);
          net_send(item);
          item_free(item);
          break;
        case 2:
          // Anyone can create pairs of public items...
          struct item *first = net_receive();
          struct item *second = net_receive();
          struct item *pair = create_pair(first, second);
          item_free(first);
          item_free(second);
          net_send(pair);
          item_free(pair);
          break;
        case 3:
          // Anyone can encrypt a public item with a published key...
          struct item *key = net_receive();
          struct item *payload = net_receive();
          check_is_key(key);
          struct item *item = encrypt(key, payload);
          //@ open key_item(key, _, _, _, _);
          item_free(key);
          item_free(payload);
          net_send(item);
          item_free(item);
          break;
        case 4:
          // Anyone can deconstruct a public pair...
          struct item *pair = net_receive();
          struct item *first = pair_get_first(pair);
          struct item *second = pair_get_second(pair);
          item_free(pair);
          net_send(first);
          item_free(first);
          net_send(second);
          item_free(second);
          break;
        case 5:
          // Anyone can decrypt a public item with a published key...
          struct item *key = net_receive();
          struct item *package = net_receive();
          check_is_key(key);
          struct item *payload = decrypt(key, package);
          //@ open key_item(key, ?kcreator, ?kid, ?keyyy, ?kinfo);
          item_free(key);
          //@ SWITCH_CRYPTO_PRIMITIVES(package, 1, 4);
          item_free(package);
          net_send(payload);
          item_free(payload);
          break;
      }
    }
    //@ leak generated_keys(_, _);
  }
}
