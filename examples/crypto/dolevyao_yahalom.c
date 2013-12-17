// See explanations in lib/dolevyao.h
#include "lib/dolevyao.h"
#include "stdlib.h"

/*

Dolev-Yao security verification of the Yahalom symmetric key protocol:

1. A -> B. A, NA 
2. B -> S. B, {A, NA, NB}_K(BS)
3. S -> A. {B, K(AB), NA, NB}_K(AS), {A, K(AB)}_K(BS)
4. A -> B. {A, K(AB)}_K(BS), {NB}_K(AB)

Goal: A and B share a symmetric encryption session key K(AB)

*/

///////////////////////////////////////////////////////////////////////////////
// Configuration for this protocol ////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

struct item *create_principal();
  //@ requires principals(?count);
  /*@ ensures  principals(count + 1) &*& generated_nonces(count, 0) &*& 
               key_item(result, count, 0, symmetric_key, int_pair(0, 0)); 
  @*/

// Principal 0 is the key server, which any principal shares a secret symmetric 
// key with
//@ predicate initial_principals() = principals(1);

/*
Encodings for this protocol
key_item:
  *For communication by participant A with the trusted server:
     sender == A &*& info == int_pair(1, 0)
  *For communication by participant A with participant B:
     sender == A &*& info == int_pair(2, B)
info for messages:
  *Encryption:
    int_pair(1, 0) : for communication with the trusted key server
    int_pair(2, B) : for communication bewteen two principals
  *Nonces:
    int_pair(3, 0): NA
    int_pair(4, int_pair(A, B)): NB
*/

///////////////////////////////////////////////////////////////////////////////
// Definition of pub for this protocol ////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

/*@

fixpoint bool mypub(item i) 
{
  switch (i) 
  {
    case pair_item(first0, second0):
      // For concatenation (Concatenations of public items are public)
      return mypub(first0) && mypub(second0);
    case nonce_item(p0, count0, info0):
      // NA & NB (NB should remain secret)
      return info0 == int_pair(3, 0) || 
             bad(p0) ||
             bad(int_left(int_right(info0))) ||
             bad(int_right(int_right(info0)));
    case key_item(s0, count0, kind0, info0):
      // K(AS) & K(BS) & K(AB) (Keys should not leak)
      return kind0 == symmetric_key && (bad(s0) || bad(int_right(info0)));
    case data_item(data0):
      // A & B
      return true;
    case encrypted_item(s0, count0, kind0, info0, p0, entropy0): return
      (mypub(p0) && (bad(s0) || bad(int_right(info0)))) ||
      switch(p0)
      {
        // {NB}_K(AB)
        case nonce_item(s1, count1, info1): return 
          kind0 == symmetric_key &&
          info0 == int_pair(2, s1) &&
          info1 == int_pair(4, int_pair(s0, s1));
        case pair_item(first1, second1): return
          switch(second1)
          {
            // {A, K(AB)}_K(BS)
            case key_item(s2, count2, kind2, info2): return
              s0 == int_right(info2) &&
              info0 == int_pair(1, 0) &&
              kind0 == symmetric_key &&
              first1 == data_item(s2) &&
              info2 == int_pair(2, s0) &&
              kind2 == symmetric_key;
            case pair_item(first2, second2): return
              switch(second2)
              {
                //{A, NA, NB}_K(BS)
                case nonce_item(s3, count3, info3): return // NB
                  switch(first1)
                  {
                    case data_item(data4): return // A
                      switch(first2)
                      {
                        case nonce_item(s5, count5, info5): return // NA
                          s0 == s3 &&
                          info0 == int_pair(1, 0) &&
                          kind0 == symmetric_key &&
                          // B cannot know this for sure
                          // data4 == s5 &&
                          info3 == int_pair(4, int_pair(data4, s3)) &&
                          (info5 == int_pair(3, 0) || 
                          bad(s5) ||
                          bad(int_left(int_right(info5))) ||
                          bad(int_right(int_right(info5))));
                        default: return false;
                      };
                    default: return false;
                  };
                // {B, K(AB), NA, NB}_K(AS)
                case pair_item(first3, second3): return
                  switch(second3)
                  {
                    case nonce_item(s4, count4, info4): return //NB
                      switch(first1)
                        {
                          case data_item(data5): return //B
                            switch(first2)
                            {
                              case key_item(s6, count6, kind6, info6): return //K(AB)
                                switch(first3)
                                {   
                                  case nonce_item(s7, count7, info7): return //NA
                                    s0 == s6 &&
                                    info0 == int_pair(1, 0) &&
                                    kind0 == symmetric_key &&
                                    info6 == int_pair(2, data5) &&
                                    kind6 == symmetric_key &&
                                      // S cannot know this for sure
                                      // s7 == s6 &&
                                    info7 == int_pair(3, 0) &&
                                    s4 == data5 &&
                                    info4 == int_pair(4, int_pair(s6, data5));
                                  default: return false;      
                                };
                              default: return false;      
                            };
                          default: return false;      
                        };
                    default: return false;     
                  };
                default: return false;
              };
            default: return false;
          };
        default: return false;
      };
    default: return false;
  }
}

@*/

///////////////////////////////////////////////////////////////////////////////
// Protocol implementation ////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

struct item *sender(int sender, int receiver, struct item *KAS)
  /*@ requires !bad(sender) &*& !bad(receiver) &*& !bad(0) &*&
               world(mypub) &*& 
               generated_nonces(sender, ?count) &*& 
               key_item(KAS, sender, 0, symmetric_key, int_pair(1,0)); 
  @*/
  /*@ ensures  world(mypub) &*&
               generated_nonces(sender, count + 1) &*& 
               key_item(KAS, sender, 0, symmetric_key, int_pair(1,0)) &*& 
               // Secrecy of KAS
               mypub(key_item(sender, 0, symmetric_key, int_pair(1, 0))) == false &*&
               key_item(result, sender, ?cab, symmetric_key, int_pair(2, receiver)) &*&
               // Secrecy of KAB
               mypub(key_item(sender, cab, symmetric_key, int_pair(2, receiver))) == false; 
  @*/
              
{
  struct item *i1;
  struct item *i2;
  struct item *i3;
  struct item *i4;
  struct item *i5;
  struct item *i6;
  struct item *i7;
  struct item *i8;
  
  struct item *A = create_data_item(sender);
  struct item *B = create_data_item(receiver);
  //@ close nonce_request(sender, int_pair(3, 0));
  struct item *NA = create_nonce();
  
  // 1. A -> B. A, NA
  i1 = create_pair(A, NA);
  net_send(i1);
  item_free(i1);
  
  // 3. S -> A. {B, K(AB), NA, NB}_K(AS), {A, K(AB)}_K(BS)
  i1 = net_receive();
  i2 = pair_get_first(i1);
  struct item *B_S = pair_get_second(i1);
  i3 = decrypt(KAS, i2);
  i4 = pair_get_first(i3); // B
    // check B
    if (!item_equals(i4, B)){abort();}
  i5 = pair_get_second(i3);
  struct item *KAB = pair_get_first(i5); // K(AB)
  i6 = pair_get_second(i5);
  i7 = pair_get_first(i6); // NA
    // check NA
    if (!item_equals(i7, NA)){abort();}
  struct item *NB = pair_get_second(i6); // NB
    // check KAB
    check_is_key(KAB);
  item_free(i1);
  item_free(i2);
  item_free(i3);
  item_free(i4);
  item_free(i5);
  item_free(i6);
  item_free(i7);
  
  // 4. A -> B. {A, K(AB)}_K(BS), {NB}_K(AB)
  i1 = encrypt(KAB, NB);
  i2 = create_pair(B_S, i1);
  //@ SWITCH_CRYPTO_PRIMITIVES(i1, 1, 2);

  net_send(i2);
  item_free(i1);
  item_free(i2);
  
    //Protocol End Goals
    ///////////////////////////////////////////////////////////////////////////
    //1) Secrecy of NB
    //@  assert item(NB, ?nb);
    //@  assert (mypub(nb) == false);
    //
    //2) Secrecy of KAS
    //@ open key_item(KAS, ?sas, ?cas, ?kindas, ?ias);
    //@ assert item(KAS, ?kas);
    //@ assert (mypub(kas) == false);
    //@ close key_item(KAS, sas, cas, kindas, ias);
    //
    //3) Secrecy of KAB
    //@ open key_item(KAB, ?sab, ?cab, ?kindab, ?iab);
    //@ assert item(KAB, ?kab);
    //@ assert (mypub(kab) == false);
    //@ close key_item(KAB, sab, cab, kindab, iab);
    ///////////////////////////////////////////////////////////////////////////

  item_free(A);
  item_free(B);
  item_free(NA);
  item_free(NB);
  item_free(B_S);
  
  return KAB;
}

void receiver(int receiver, struct item * KBS)
  /*@ requires !bad(receiver) &*& !bad(0) &*&
               world(mypub) &*& 
               generated_nonces(receiver, ?count) &*&
               key_item(KBS, receiver, 0, symmetric_key, int_pair(1,0)); 
  @*/
  /*@ ensures  world(mypub) &*& 
               generated_nonces(receiver, count + 1) &*& 
               key_item(KBS, receiver, 0, symmetric_key, int_pair(1,0)); 
  @*/
{
  struct item *i1;
  
  // 1. A -> B. A, NA
  i1 = net_receive();
  struct item *A = pair_get_first(i1);
  int sender = item_get_data(A);
  struct item *NA = pair_get_second(i1); // NA
    // check NA
    check_is_nonce(NA);
  item_free(i1);
  
  struct item* KAB = core_receiver(sender, NA, receiver, KBS);
  
  item_free(A);
  //@ open key_item(KAB, _, _, _, _);
  item_free(KAB);
}
    
struct item *core_receiver(int sender, struct item* NA, int receiver, struct item * KBS)
  /*@ requires !bad(receiver) &*& !bad(0) &*&
               world(mypub) &*& 
               generated_nonces(receiver, ?count) &*&
               key_item(KBS, receiver, 0, symmetric_key, int_pair(1,0)) &*&
               item(NA, nonce_item(?p, ?c, ?i)) &*& 
               mypub(nonce_item(p, c, i)) == true; 
  @*/
  /*@ ensures  world(mypub) &*& 
               generated_nonces(receiver, count + 1) &*& 
               key_item(KBS, receiver, 0, symmetric_key, int_pair(1,0)) &*&
               // Secrecy of KBS
               mypub(key_item(receiver, 0, symmetric_key, int_pair(1, 0))) == false &*&
               key_item(result, sender, ?cab, symmetric_key, int_pair(2, receiver)) &*&
               // Secrecy of KAB
               bad(sender) || 
               mypub(key_item(sender, cab, symmetric_key, int_pair(2, receiver))) == false; 
  @*/
{
  struct item *i1;
  struct item *i2;
  struct item *i3;
  struct item *i4;
  struct item *i5;
  struct item *i6;
  
  struct item *A = create_data_item(sender);
  struct item *B = create_data_item(receiver);
  
  // 2. B -> S. B, {A, NA, NB}_K(BS)
  //@ close nonce_request(receiver, int_pair(4, int_pair(sender, receiver)));
  struct item *NB = create_nonce();
  i1 = create_pair(NA, NB);
  i2 = create_pair(A, i1);
  i3 = encrypt(KBS, i2);
  i4 = create_pair(B, i3);
  net_send(i4);
  item_free(i1);
  item_free(i2);
  item_free(i3);
  item_free(i4);
  
  // 4. A -> B. {A, K(AB)}_K(BS), {NB}_K(AB)
  i1 = net_receive();
  i2 = pair_get_first(i1); // {A, K(AB)}_K(BS)
  i3 = pair_get_second(i1); // {NB}_K(AB)
  i4 = decrypt(KBS, i2);
  i5 = pair_get_first(i4); // A
    // check A
    if (!item_equals(i5, A)){abort();}
  struct item *KAB = pair_get_second(i4); // K(AB)
    // check KAB
    check_is_key(KAB);
  i6 = decrypt(KAB, i3); // NB
    // check NB
    if (!item_equals(i6, NB)){abort();}
  
  item_free(i1);
  item_free(i2);
  item_free(i3);
  item_free(i4);
  item_free(i5);
  item_free(i6);

    //Protocol End Goals
    ///////////////////////////////////////////////////////////////////////////
    //These goals are conditionally met: i.e. if the sender is not bad 
    //(otherwise the sender could leak the key or nonce)
  
    //1) Secrecy of NB
    //@  assert item(NB, ?nb);
    //@  assert bad(sender) || (mypub(nb) == false);
    //
    //2) Secrecy of KBS
    //@ open key_item(KBS, ?sbs, ?cbs, ?kindbs, ?ibs);
    //@ assert item(KBS, ?kbs);
    //@ assert (mypub(kbs) == false);
    //@ close key_item(KBS, sbs, cbs, kindbs, ibs);
    //
    //3) Secrecy of KAB
    //@ open key_item(KAB, ?sab, ?cab, ?kindab, ?iab);
    //@ assert item(KAB, ?kab);
    //@ assert bad(sender) || (mypub(kab) == false);
    //@ close key_item(KAB, sab, cab, kindab, iab);
    ///////////////////////////////////////////////////////////////////////////
    
  item_free(A);
  item_free(B);
  item_free(NA);
  item_free(NB);
  
  return KAB;
}

///////////////////////////////////////////////////////////////////////////////
// Attacker representation ////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////    

void attacker()
  //@ requires world(mypub) &*& initial_principals() &*& !bad(0);
  //@ ensures false;
{
  //@ open initial_principals();
  for (;;)
    //@ invariant world(mypub) &*&  principals(_);
  {
    // Attackers are arbitrary principals.
    struct item *server_key = create_principal();
    for (;;)
      /*@ 
          invariant world(mypub) &*& principals(_) &*&
                    generated_nonces(?me, 0) &*&
                    key_item(server_key, me, 0, symmetric_key, int_pair(0, 0)); 
      @*/
    {
      int action = choose();
      switch (action) 
      {
        case 0:
          // Bad principals leak their server key...
          //@ assume(bad(me));
          //@ open key_item(server_key, me, 0, symmetric_key, int_pair(0, 0));
          net_send(server_key);
          //@ close key_item(server_key, me, 0, symmetric_key, int_pair(0, 0));
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
        case 4:
          // Anyone can encrypt a public item with a published key...
          struct item *key = net_receive();
          struct item *payload = net_receive();
          int sender = choose();
          int receiver = choose();
          check_is_key(key);
          struct item *item = encrypt(key, payload);
          net_send(item);
          //@ open key_item(key, _, _, _, _);
          item_free(key);
          item_free(payload);
          item_free(item);
          break;
        case 5:
          // Anyone can decrypt a public item with a published key...
          struct item *key = net_receive();
          struct item *package = net_receive();
          int sender = choose();
          int receiver = choose();
          check_is_key(key);
          struct item *payload = decrypt(key, package);
          //@ SWITCH_CRYPTO_PRIMITIVES(payload, 1, 4);
          net_send(payload);
          item_free(package);
          item_free(payload);
          //@ open key_item(key, _, _, _, _);
          item_free(key);
          break;
      }
    }
    break;
  }
}
