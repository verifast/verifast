#ifndef NSL_H
#define NSL_H

// See explanations in ../../include/cryptolib.h
#include "../../include/cryptolib.h"

/*

Dolev-Yao security verification of the Needham-Schroeder-Lowe public key
authentication protocol:

1. A -> B. {A,NA}_K(B)
2. B -> A. {B,NA,NB}_K(A)
3. A -> B. {NB}_K(B)

Goal: Secrets NA and NB shared between A and B

Client: A
Server: B

*/

///////////////////////////////////////////////////////////////////////////////
// Encodings for this protocol ////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

/*
info:
  int_pair(0, 0): for encryption
  int_pair(1, server): client nonce
  int_pair(2, int_pair(client, server)): server nonce
*/

///////////////////////////////////////////////////////////////////////////////
// Definition of pub for this protocol ////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

/*@
// A definition of "pub" for the example protocol.
fixpoint bool nsl_pub(item i)
{
  switch (i)
  {
    case pair_item(first0, second0):
      return nsl_pub(first0) && nsl_pub(second0);
    case data_item(data0):
      return true;
    case key_item(p0, count0, kind0, info0):
      return bad(p0);
    case hmac_item(key0, pay0):
      return true;
    case nonce_item(p0, count0, int0, info0): return
      bad(p0) ||
        (int_left(info0) == 1 && bad(int_right(info0))) ||
        (int_left(info0) == 2 && bad(int_left(int_right(info0))));
    case encrypted_item(key0, pay0, ent0): return
      switch(key0)
      {
        case key_item(p0, count0, kind0, info0): return
          nsl_pub(key0) && nsl_pub(pay0) ||
          
          switch(pay0)
          {
            // {NB}_K(B)
            case nonce_item(p1, count1, inc1, info1): return
              p0 == p1 &&
              int_left(info1) == 2 &&
              int_right(int_right(info1)) == p0;
            case pair_item(f1, s1): return
              switch(s1)
              {
                case nonce_item(p2, count2, inc2, info2): return
                  switch(f1)
                  {
                    case data_item(d3): return
                      p2 == d3 && info2 == int_pair(1, p0);
                    default: return false;
                  };
                case pair_item(f2, s2): return
                  switch(s2)
                  {
                    case nonce_item(p3, count3, inc3, info3): return // NB
                      switch(f1)
                      {
                        case data_item(d4): return // B
                          switch(f2)
                          {
                            case nonce_item(p5, count5, id5, info5): return // NA
                              // {B,NA,NB}_K(A)
                              p3 == d4 &&
                              info3 == int_pair(2, int_pair(p0, p3)) &&
                              p5 == p0 && info5 == int_pair(1, d4);
//                               (
//                                 bad(p5) ||
//                                 (int_left(info5) == 1 && bad(int_right(info5))) ||
//                                 (int_left(info5) == 2 && bad(int_left(int_right(info5)))) ||
//                                 ()
//                               );
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
// Implementation prototypes for this protocol ////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

void sender(int sender, int receiver, struct item *KA_PRIVATE, struct item *KB);
  /*@ requires [?f0]world(nsl_pub) &*&
               generated_values(sender, _) &*&
               !bad(sender) &*& !bad(receiver) &*&
               item(KA_PRIVATE, ?kap) &*& item(KB, ?kb) &*&
               kap == key_item(sender, ?count_kap, private_key, int_pair(0, 0)) &*&
               kb == key_item(receiver, ?count_kb, public_key, int_pair(0, 0));
  @*/
  /*@ ensures  [f0]world(nsl_pub) &*&
               generated_values(sender, _) &*&
               item(KA_PRIVATE, kap) &*& item(KB, kb);
  @*/

void receiver(int receiver, struct item *KB_PRIVATE);
  /*@ requires [?f0]world(nsl_pub) &*&
               generated_values(receiver, _) &*& !bad(receiver) &*&
               item(KB_PRIVATE, ?kbp) &*&
               kbp == key_item(receiver, ?sskid, private_key, int_pair(0, 0));
  @*/
  /*@ ensures  [f0]world(nsl_pub) &*&
               generated_values(receiver, _) &*& !bad(receiver) &*&
               item(KB_PRIVATE, kbp);
  @*/

///////////////////////////////////////////////////////////////////////////////
// Attacker proof obligations for this protocol ///////////////////////////////
///////////////////////////////////////////////////////////////////////////////

/*@
  DEFAULT_CAN_SEND_DATA(nsl)
  DEFAULT_CAN_SEND_PUBLIC_PAIR(nsl)
  DEFAULT_CAN_SEND_DECOMPOSED_PUBLIC_PAIR(nsl)
  DEFAULT_CAN_SEND_BAD_PRINCIPAL_NONCE(nsl)
  DEFAULT_CAN_SEND_INCREMENTED_NONCE(nsl)
  DEFAULT_CAN_SEND_BAD_PRINCIPAL_KEYS(nsl)
  DEFAULT_CAN_SEND_PUBLIC_HMAC(nsl)
  DEFAULT_CAN_SEND_PUBLIC_ENCRYPTED(nsl)
  DEPTH_CAN_SEND_PUBLIC_DECRYPTED(nsl, 4)
@*/

#endif
