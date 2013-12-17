// See explanations in lib/dolevyao.h
#include "lib/dolevyao.h"
#include "stdlib.h"

/*

Dolev-Yao security verification of a simple secure storage protocol

*/

///////////////////////////////////////////////////////////////////////////////
// Configuration for this protocol ////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

/*@

lemma void create_principal();
    requires principals(?count);
    ensures principals(count + 1) &*& generated_keys(count, 0);

@*/

//@ fixpoint bool app_send_event(int sender, item message);

///////////////////////////////////////////////////////////////////////////////
// Definition of pub for this protocol ////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

/*@

fixpoint bool mypub(item i) {
    switch (i) {
        case key_item(p, c, k, info): return bad(p);
        case data_item(d): return true;
        case hmac_item(creator, id, info, m): 
          return bad(creator) || app_send_event(creator, m);
        case pair_item(i1, i2): return mypub(i1) && mypub(i2);
        default: return false;
    }
}

@*/

///////////////////////////////////////////////////////////////////////////////
// Protocol implementation ////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

void app_send(struct item *key, struct item *message)
    /*@ requires world(mypub) &*& key_item(key, ?creator, ?id, symmetric_key, 0) &*& 
                 item(message, ?msg) &*& mypub(msg) == true &*& 
                 app_send_event(creator, msg) == true; 
    @*/
    /*@ ensures  world(mypub) &*& key_item(key, creator, id, symmetric_key, 0) &*& 
                 item(message, msg); 
    @*/
{
    struct item *hash = hmac(key, message);
    struct item *m = create_pair(hash, message);
    item_free(hash);
    net_send(m);
    item_free(m);
}

struct item *app_receive(struct item *key)
    /*@ requires world(mypub) &*& 
                 key_item(key, ?creator, ?id, symmetric_key, 0); 
    @*/
    /*@ ensures world(mypub) &*& 
                key_item(key, creator, id, symmetric_key, 0) &*& 
                item(result, ?msg) &*& bad(creator) || 
                app_send_event(creator, msg); 
    @*/
{
    struct item *m = net_receive();
    struct item *hash = pair_get_first(m);
    struct item *message = pair_get_second(m);
    item_free(m);
    hmacsha1_verify(hash, key, message);
    item_free(hash);
    return message;
}

///////////////////////////////////////////////////////////////////////////////
// Attacker representation ////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

void attacker()
    //@ requires world(mypub) &*& principals(0);
    //@ ensures false;
{
    for (;;)
        //@ invariant world(mypub) &*& principals(_);
    {
        //@ create_principal(); // Attackers are arbitrary principals.
        for (;;)
            /*@ invariant world(mypub) &*& principals(_) &*& 
                          generated_keys(?me, ?keyCount); @*/
        {
            int action = choose();
            switch (action) {
                case 0:
                    //@ assume(bad(me));
                    //@ close key_request(me, 0);
                    struct item *item = create_key();
                    //@ open key_item(item, _, _, _, _);
                    net_send(item);
                    item_free(item);
                    break;
                case 1:
                    int data = choose();
                    struct item *item = create_data_item(data);
                    net_send(item);
                    item_free(item);
                    break;
                case 2:
                    struct item *first = net_receive();
                    struct item *second = net_receive();
                    struct item *pair = create_pair(first, second);
                    item_free(first);
                    item_free(second);
                    net_send(pair);
                    item_free(pair);
                    break;
                case 3:
                    struct item *key = net_receive();
                    struct item *payload = net_receive();
                    check_is_key(key);
                    struct item *hash = hmac(key, payload);
                    //@ open key_item(key, _, _, _, _);
                    item_free(key);
                    item_free(payload);
                    net_send(hash);
                    item_free(hash);
                    break;
                case 4:
                    struct item *pair = net_receive();
                    struct item *first = pair_get_first(pair);
                    struct item *second = pair_get_second(pair);
                    item_free(pair);
                    net_send(first);
                    item_free(first);
                    net_send(second);
                    item_free(second);
                    break;
            }
        }
        //@ leak principal(_, _);
    }
}