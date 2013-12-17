/*

Dolev-Yao security verification of the Needham-Schroeder symmetric key protocol:

1. A -> B. A
2. B -> A. {A, NB1}_K(BS)
3. A -> S. A, B, NA, {A, NB1}_K(BS)
4. S -> A. {NA, K(AB), B, {K(AB), A, NB1}_K(BS)}_K(AS)
5. A -> B. {K(AB), A, NB1}_K(BS)
6. B -> A. {NB2}_K(AB)
7. A -> B. {NB2 + 1}_K(AB)

Goal: A and B share a symmetric encryption session key K(AB)

*/

#include "stdlib.h"

///////////////////////////////////////////////////////////////////////////////
// Encodings for this protocol ////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

// key_item:
//   *For communication by participant A with the trusted server:
//      sender == A &*& receiver == 0 &*& count == 0
//   *For communication by participant A with participant B:
//      sender == A &*& receiver == B

// info for messages:
//   *Encryption:
//     int_pair(0, 1) : for communication with the trusted key server
//     int_pair(0, 1) : for communication bewteen two principals
//   *Nonces:
//     int_pair(1, A): NA
//     int_pair(2, int_pair(A, B)): NB1 
//     int_pair(3, int_pair(A, B)): NB2
//     int_pair(4, int_pair(3, int_pair(A, B))): NB2 + 1

///////////////////////////////////////////////////////////////////////////////
// Configuration for this protocol ////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

#include "dolevyao.h"

// Principal 0 is the key server, which any principal shares a secret symmetric key with
//@ predicate initial_principals() = principals(1);

struct item *create_principal();
  //@ requires principals(?count);
  /*@ ensures principals(count + 1) &*& generated_nonces(count, 0) &*& 
              key_item(result, count, 0, 0, int_pair(0, 0)); @*/

///////////////////////////////////////////////////////////////////////////////
// Definition of pub for this protocol ////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

/*@
// A definition of "pub" for the example protocol.
fixpoint bool mypub(item i) 
{
  switch (i) 
  {
    case nonce_item(p0, count0, info0):
      // e.g. NA
      return true;
//       return bad(p0) || info0 == int_pair(1, p0);
    case key_item(s0, r0, count0, info0):
      // Should not happen
      return bad(s0) || bad(r0);
    case data_item(data0):
      // e.g. A or B
      return true;
    case pair_item(first0, second0):
      // For concatenation
      return mypub(first0) && mypub(second0);
    case encrypted_item(s0, r0, count0, info0, p0, entropy0): return 
      mypub(p0) ||
      switch(p0)
      {
        case nonce_item(s1, count1, info1): return 
          info0 == int_pair(0,1) && r0 == s1 &&
          (
            // {NB2}_K(AB)
            info1 == int_pair(3, int_pair(s0, r0)) ||
            // {NB2 + 1}_K(AB)
            info1 == int_pair(4, int_pair(3, int_pair(s0, r0)))
          );      
        case pair_item(first1, second1): return 
          r0 == 0 && count0 == 0 && info0 == int_pair(0,0) && 
          switch(second1)
          {
            // {A, NB1}_K(BS)
            case nonce_item(s2, count2, info2): return
              s2 == s0 && 
              switch(first1)
              {
                case data_item(s3): return
                  info2 == int_pair(2, int_pair(s3, s0));
                default: return false;
              };
            case pair_item(first2, second2): return
              switch(second2)
              {
                //{K(AB), A, NB1}_K(BS)
                case nonce_item(s3, count3, info3): return
                  //K(AB)
                  switch(first1)
                  {
                    case key_item(s4, r4, count4, info4): return
                      s4 == s0 && r4 == r0 && count4 == count0 &&
                      info4 == int_pair(0, 1);
                    default: return false;
                  } &&
                  //A
                  first2 == data_item(s0) &&
                  //NB1
                  s3 == r0 && info3 == int_pair(2, int_pair(s0, r0));
                //{NA, K(AB), B, {K(AB), A, NB1}_K(BS)}_K(AS)
                case pair_item(first3, second3): return
                  //NA
                  switch(first1)
                  {
                    case nonce_item(s5, count5, info5): return
                      s5 == s0 && info5 == int_pair(2, int_pair(s0, r0));
                    default: return false;
                  } &&
                  //K(AB)
                  switch(first2)
                  {
                    case key_item(s4, r4, count4, info4): return
                      s4 == s0 && r4 == r0 &&
                      info4 == int_pair(0, 1);
                    default: return false;
                  } &&
                  //B
                  first3 == data_item(r0) &&
                  // {K(AB), A, NB1}_K(BS)
                  mypub(second3);
                default: return false;
              };
            default: return false;
          };
        default: return false;
      };
  }
}

@*/

///////////////////////////////////////////////////////////////////////////////
// Protocol implementation ////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

void sender(int sender, int receiver, struct item * KAS)
  /*@
      requires 
        generated_nonces(sender, ?count) &*& world(mypub) &*& 
        key_item(KAS, sender, 0, 0, int_pair(0,0)) &*&
        !bad(sender) &*& !bad(receiver);
  @*/
  /*@
      ensures 
        generated_nonces(sender, count + 1) &*& world(mypub) &*& 
        key_item(KAS, sender, 0, 0, int_pair(0,0));
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
  //@ close nonce_request(sender, int_pair(1, sender));
  struct item *NA = create_nonce();
  
  // 1. A -> B. A
  net_send(A);
  
  // 2. B -> A. {A, NB1}_K(BS)
  struct item *B_S1 = net_receive();
    
  // 3. A -> S. A, B, NA, {A, NB1}_K(BS)
  i1 = create_pair(NA, B_S1); // (NA, {A, NB1}_K(BS))
  i2 = create_pair(B, i1); // (B, (NA, {A, NB1}_K(BS)))
  i3 = create_pair(A, i2); // (A, B, (NA, {A, NB1}_K(BS))))
  net_send(i3);
  item_free(i1);
  item_free(i2);
  item_free(i3);
  
  // 4. S -> A. {NA, K(AB), B, {K(AB), A, NB1}_K(BS)}_K(AS)
  i1 = net_receive();
  i2 = decrypt(KAS, i1); // (NA, (K(AB), (B, {K(AB), A, NB1}_K(BS))))
  i3 = pair_get_first(i2); // NA
  i4 = pair_get_second(i2); // (K(AB), (B, {K(AB), A, NB1}_K(BS)))
  struct item *KAB = pair_get_first(i4); // K(AB)
  i5 = pair_get_second(i4); // (B, {K(AB), A, NB1}_K(BS))
  i6 = pair_get_first(i5); // B
  struct item *B_S2 = pair_get_second(i5); // {K(AB), A, NB1}_K(BS)
    // check NA
    if (!item_equals(i3, NA)){abort();}
    // check B
    if (!item_equals(i6, B)){abort();}
    // check KAB
    check_is_key(KAB);
  item_free(i1);
  item_free(i2);
  item_free(i3);
  item_free(i4);
  item_free(i5);
  item_free(i6);
  
  // 5. A -> B. {K(AB), A, NB1}_K(BS)
  net_send(B_S2);
  
  // 6. B -> A. {NB2}_K(AB)
  i1 = net_receive();
  struct item *NB2 = decrypt(KAB, i1); // NB2
    // check NB2
    check_is_nonce(NB2);
  item_free(i1);
  
  // 7. A -> B. {NB2 + 1}_K(AB)
  i1 = increment_nonce(NB2, 4); // NB2 + 1
  i2 = encrypt(KAB, i1); // {NB2 + 1}_K(AB)
  net_send(i2);
  item_free(i1);
  item_free(i2);
  
  //@ open key_item(KAB, _, _, _, _);
  //@ assert item(KAB, ?kab);
  //TODO: //@ assert !mypub(kab);
  //@ assert item(NB2, ?nb2);
  //TODO: //@ assert !mypub(nb2);
  
  item_free(NA);
  item_free(A);
  item_free(B);
  item_free(NB2);
  item_free(B_S1);
  item_free(B_S2);
  item_free(KAB);
}

void receiver(int receiver, struct item * KBS)
  /*@
      requires 
        generated_nonces(receiver, ?count) &*& world(mypub) &*&
        key_item(KBS, receiver, 0, 0, int_pair(0,0)) &*& !bad(receiver);
  @*/
  /*@
      ensures 
        generated_nonces(receiver, count + 2) &*& world(mypub) &*& 
        key_item(KBS, receiver, 0, 0, int_pair(0,0));
  @*/
{
  struct item *i1;
  struct item *i2;
  struct item *i3;
  struct item *i4;
  struct item *i5;
  
  struct item *B = create_data_item(receiver);
  
  // 1. A -> B. A
  struct item *A = net_receive();
  int sender = item_get_data(A);
  
  // 2. B -> A. {A, NB1}_K(BS)
  //@ close nonce_request(receiver, int_pair(2, int_pair(sender, receiver)));
  struct item *NB1 = create_nonce();
  i1 = create_pair(A, NB1); // (A, NB1)
  i2 = encrypt(KBS, i1); // {A, NB1}_K(BS)
  net_send(i2);
  item_free(i1);
  item_free(i2);
  
  // 5. A -> B. {K(AB), A, NB1}_K(BS)
  i1 = net_receive();
  i2 = decrypt(KBS, i1); // (K(AB), (A, NB1))
  struct item *KAB = pair_get_first(i2); // K(AB)
  i3 = pair_get_second(i2); // (A, NB1)
  i4 = pair_get_first(i3); // A
  i5 = pair_get_second(i3); // NB1
    // check A
    if (!item_equals(i4, A)){abort();}
    // check NB1
    if (!item_equals(i5, NB1)){abort();}
    // check KAB
    check_is_key(KAB);
  item_free(i1);
  item_free(i2);
  item_free(i3);
  item_free(i4);
  item_free(i5);
  
  // 6. B -> A. {NB2}_K(AB)
  //@ close nonce_request(receiver, int_pair(3, int_pair(sender, receiver)));
  struct item *NB2 = create_nonce();
  i1 = encrypt(KAB, NB2); // {NB2}_K(AB)
  net_send(i1);
  item_free(i1);
  
  // 7. A -> B. {NB2 + 1}_K(AB)
  i1 = net_receive();
  struct item *NB2_11 = decrypt(KAB, i1); // NB2 + 1
  struct item *NB2_12 = increment_nonce(NB2, 4);
    // check NB2 + 1
    if (!item_equals(NB2_11, NB2_12)){abort();}
  item_free(i1);
  
  //@ open key_item(KAB, _, _, _, _);
  //@ assert item(KAB, ?kab);
  //TODO: //@ assert !mypub(kab);
  //@ assert item(NB1, ?nb1);
  //TODO: //@ assert !mypub(nb1);
  //@ assert item(NB2, ?nb2);
  //TODO: //@ assert !mypub(nb2);

  item_free(A);
  item_free(B);
  item_free(NB1);
  item_free(NB2);
  item_free(NB2_11);
  item_free(NB2_12);
  item_free(KAB);
}

///////////////////////////////////////////////////////////////////////////////
// Attacker representation ////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////    

int choose();
  //@ requires true;
  //@ ensures true;

void attacker()
  //@ requires world(mypub) &*& initial_principals();
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
                    key_item(server_key, me, 0, 0, int_pair(0, 0)); 
      @*/
    {
      int action = choose();
      switch (action) 
      {
        case 0:
          // Bad principals leak their server key...
          //@ assume(bad(me));
          //@ open key_item(server_key, me, 0, 0, int_pair(0, 0));
          net_send(server_key);
          //@ close key_item(server_key, me, 0, 0, int_pair(0, 0));
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
          //@ assert item(payload, _);
          //@ open key_item(key, _, _, _, _);
          item_free(key);
          item_free(package);
          //@ assert item(payload, ?p);
          /*@
              if (mypub(p)) 
              {
              } 
              else 
              {
                switch (p) 
                {
                  case nonce_item(p0, count0, info0): p = p;
                  case key_item(s0, r0, count0, info0): p = p;
                  case data_item(data0): p = p;
                  case encrypted_item(s0, r0, count0, info0, p0, entropy0): p = p;
                  case pair_item(first0, second0):
                    p = p;
                    switch (second0) 
                    {
                      // {A, NB1}
                      case nonce_item(p1, count1, info1): 
                        p = p;
                        assert (first0 == data_item(_));
                      case key_item(s1, r1, count1, info1): p = p;
                      case data_item(data1): p = p;
                      case encrypted_item(s1, r1, count1, info1, p1, entropy1): p = p;
                      case pair_item(first1, second1):
                        p = p;
                        switch (second1) 
                        {
                          // {K(AB), A, NB1}
                          case nonce_item(p2, count2, info2): 
                            p = p;
                            assert (first0 == key_item(sender, receiver, _, _));
                          case key_item(s2, r2, count2, info2): p = p;
                          case data_item(d2): p = p;
                          case encrypted_item(s2, r2, count2, info2, payload2, entropy2): p = p;
                          // {NA, K(AB), B, {K(AB), A, NB1}
                          case pair_item(first2, second2):
                            p = p;
                            switch (first1)
                            {
                              case nonce_item(p3, count3, info3): p = p;
                              case key_item(s3, r3, count3, info3):
                                p = p;
                                assert (first0 == key_item(sender, receiver, _, _));
                              case data_item(d3): p = p;
                              case encrypted_item(s3, r3, count3, info3, payload3, entropy3): p = p;
                              case pair_item(first3, second3): p = p;
                            }
                        }
                   }
                }
              }
          @*/
          net_send(payload);
          item_free(payload);
          break;
      }
    }
    break;
  }
}











//4. S -> A. {NA, K(AB), B, {K(AB), A, NB1}_K(BS)}_K(AS)

// /*@
// lemma void retrieve_key_info(struct item* message);
//   requires item(message, ?encrypted) &*&
//            encrypted == encrypted_item(?s0, ?r0, ?c0, ?i0, ?p0, ?e0) &*&
//            p0 == pair_item(?first01, ?second01) &*&
//            second01 == pair_item(?first02, ?second02) &*&
//            first02 == key_item(_, _, _, _) &*&
//            second02 == pair_item(?first03, ?second03) &*&
//            first03 == data_item(?r04) &*&          
//            world(?mypub) &*& mypub(encrypted) == true;
//   ensures item(message, encrypted) &*&
//           first02 == key_item(s0, r04, _, int_pair(0,1));
// {
//   switch (encrypted) 
//   {
//     case nonce_item(p1, count1, info1):
//     case key_item(s1, r1, count1, info1):
//     case data_item(data1):
//     case pair_item(first1, second1):
//     case encrypted_item(s1, r1, count1, info1, p1, entropy1):
//       if (mypub(p1)) 
//       {
//         switch (p1)
//         {
//           case nonce_item(p2, count2, info2):
//           case key_item(s2, r2, count2, info2):
//           case data_item(data2):
//           case encrypted_item(s2, r2, count2, info2, p2, entropy2):
//           case pair_item(first2, second2): 
//             switch (second2)
//             {
//               case nonce_item(p3, count3, info3):
//               case key_item(s3, r3, count3, info3):
//               case data_item(data3):
//               case encrypted_item(s3, r3, count3, info3, p3, entropy3):
//               case pair_item(first3, second3): 
//                 switch (second3)
//                 {
//                   case nonce_item(p4, count4, info4):
//                   case key_item(s4, r4, count4, info4):
//                   case data_item(data4):
//                   case encrypted_item(s4, r4, count4, info4, p4, entropy4):
//                   case pair_item(first4, second4):
//                     switch (first3)
//                     {
//                       case nonce_item(p5, count5, info5):
//                       case key_item(s5, r5, count5, info5): 
//                         assert !mypub(first3);
//                       case data_item(data5):
//                       case encrypted_item(s5, r5, count5, info5, p5, entropy5):
//                       case pair_item(first5, second5):
//                     } 
//                 }    
//             }    
//          }
//       }
//       else
//       {
//         switch (p0)
//         {
//           case nonce_item(p2, count2, info2):
//           case key_item(s2, r2, count2, info2):
//           case data_item(data2):
//           case encrypted_item(s2, r2, count2, info2, p2, entropy2):
//           case pair_item(first2, second2): 
//             switch (second2)
//             {
//               case nonce_item(p3, count3, info3):
//               case key_item(s3, r3, count3, info3):
//               case data_item(data3):
//               case encrypted_item(s3, r3, count3, info3, p3, entropy3):
//               case pair_item(first3, second3): 
//                 switch (second3)
//                 {
//                   case nonce_item(p4, count4, info4):
//                   case key_item(s4, r4, count4, info4):
//                   case data_item(data4):
//                   case encrypted_item(s4, r4, count4, info4, p4, entropy4):
//                   case pair_item(first4, second4):
//                     switch (first2)
//                     {
//                       case nonce_item(p5, count5, info5):
//                       case key_item(s5, r5, count5, info5): 
//                         assert s5 == sender;
//                       case data_item(data5):
//                       case encrypted_item(s5, r5, count5, info5, p5, entropy5):
//                       case pair_item(first5, second5):
//                     } 
//                 }    
//             }    
//          }
//       }
//   }
// }
// @*/

//   //@ assert item(i1, ?m);
//     /*@
//         
//           case nonce_item(p0, count0, info0): m = m;
//           case key_item(s0, r0, count0, info0): m = m;
//           case data_item(data0): m = m;
//           case encrypted_item(s0, r0, count0, info0, p0, entropy0): 
//             m = m;
//             if (mypub(p0)) 
//             {
//               switch (p0)
//               {
//                 case nonce_item(p1, count1, info1): m = m;
//                 case key_item(s1, r1, count1, info1): m = m;
//                 case data_item(data1): m = m;
//                 case encrypted_item(s1, r1, count1, info1, p1, entropy1): m = m;
//                 case pair_item(first1, second1): 
//                   m = m;
//                   switch (second1)
//                   {
//                     case nonce_item(p2, count2, info2): m = m;
//                     case key_item(s2, r2, count2, info2): m = m;
//                     case data_item(data2): m = m;
//                     case encrypted_item(s2, r2, count2, info2, p2, entropy2): m = m;
//                     case pair_item(first2, second2): 
//                       m = m;
//                       switch (second2)
//                       {
//                         case nonce_item(p3, count3, info3): m = m;
//                         case key_item(s3, r3, count3, info3): m = m;
//                         case data_item(data3): m = m;
//                         case encrypted_item(s3, r3, count3, info3, p3, entropy3): m = m;
//                         case pair_item(first3, second3):
//                           m = m;
//                           switch (first2)
//                           {
//                             case nonce_item(p4, count4, info4): m = m;
//                             case key_item(s4, r4, count4, info4): 
//                               m = m;
//                               
//                             case data_item(data4): m = m;
//                             case encrypted_item(s4, r4, count4, info4, p4, entropy4): m = m;
//                             case pair_item(first4, second4): m = m;
//                           } 
//                       }    
//                   }    
//               } 
//             }
//             else 
//             {
//               switch (p0)
//               {
//                 case nonce_item(p1, count1, info1): m = m;
//                 case key_item(s1, r1, count1, info1): m = m;
//                 case data_item(data1): m = m;
//                 case encrypted_item(s1, r1, count1, info1, p1, entropy1): m = m;
//                 case pair_item(first1, second1): 
//                   m = m;
//                   switch (second1)
//                   {
//                     case nonce_item(p2, count2, info2): m = m;
//                     case key_item(s2, r2, count2, info2): m = m;
//                     case data_item(data2): m = m;
//                     case encrypted_item(s2, r2, count2, info2, p2, entropy2): m = m;
//                     case pair_item(first2, second2): 
//                       m = m;
//                       switch (second2)
//                       {
//                         case nonce_item(p3, count3, info3): m = m;
//                         case key_item(s3, r3, count3, info3): m = m;
//                         case data_item(data3): m = m;
//                         case encrypted_item(s3, r3, count3, info3, p3, entropy3): m = m;
//                         case pair_item(first3, second3): 
//                           m = m;
//                           switch (first2)
//                           {
//                             case nonce_item(p4, count4, info4): m = m;
//                             case key_item(s4, r4, count4, info4): 
//                               m = m;
//                               assert s4 == sender;
//                             case data_item(data4): m = m;
//                             case encrypted_item(s4, r4, count4, info4, p4, entropy4): m = m;
//                             case pair_item(first4, second4): m = m;
//                           } 
//                       }    
//                   }    
//               } 
//             }   
//           case pair_item(first0, second0): m = m;
//         }
//     @*/
//     //@ assert key_item(KAB, _, _, _, _);
//     //@ assert key_item(KAB, _, _, _, int_pair(0, 1));








