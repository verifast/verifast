#include "secure_storage.h"
#include "stdlib.h"

#define APP_RECEIVE_PORT 121212

void app_send(struct item *key, struct item *message)
  /*@ requires [?f0]world(ss_pub, ss_key_clsfy) &*& principal(?p, ?c) &*&
               item(key, symmetric_key_item(?creator, ?id), ss_pub) &*& 
               item(message, ?msg, ss_pub) &*& [_]ss_pub(msg) &*&
               app_send_event(creator, msg) == true;
  @*/
  /*@ ensures  [f0]world(ss_pub, ss_key_clsfy) &*& principal(p, c) &*&
               item(key, symmetric_key_item(creator, id), ss_pub) &*&
               item(message, msg, ss_pub);
  @*/
{
    struct network_status *net_stat = 
                                 network_connect("localhost", APP_RECEIVE_PORT);
    struct item *hash = create_hmac(key, message);
    //@ assert item(hash, ?h, ss_pub);
    //@ close ss_pub(h);
    //@ leak ss_pub(h);
    struct item *m = create_pair(hash, message);
    //@ assert item(m, ?pmessage, ss_pub);
    //@ close ss_pub(pmessage);
    //@ leak ss_pub(pmessage);
    network_send(net_stat, m);
    item_free(hash);
    item_free(m);
    
    network_disconnect(net_stat);
}

struct item *app_receive(struct item *key)
  /*@ requires [?f0]world(ss_pub, ss_key_clsfy) &*& principal(?p, ?c) &*&
               item(key, symmetric_key_item(?creator, ?id), ss_pub);
  @*/
  /*@ ensures  [f0]world(ss_pub, ss_key_clsfy) &*& principal(p, c) &*&
               item(key, symmetric_key_item(creator, id), ss_pub) &*&
               item(result, ?msg, ss_pub) &*& 
               col || bad(creator) || app_send_event(creator, msg);
  @*/
{
    struct network_status *net_stat = network_bind_and_accept(APP_RECEIVE_PORT);
    
    struct item *m = network_receive(net_stat);
    struct item *hmac1 = pair_get_first(m);
    struct item *message = pair_get_second(m);
    //@ assert item(message, ?msg, ss_pub);
    //@ open [_]ss_pub(_);
    //@ if (col) {close ss_pub(msg); leak [_]ss_pub(msg);}
    struct item *hmac2 = create_hmac(key, message);
    item_check_equal(hmac1, hmac2);
    //@ assert item(m, pair_item(?hmac_i, ?message_i), ss_pub);
    //@ open [_]ss_pub(pair_item(hmac_i, message_i));
    //@ if (!col) open [_]ss_pub(hmac_i);
    //@ if (!col) open [_]ss_pub(message_i);
    item_free(m);
    item_free(hmac1);
    item_free(hmac2);
    
    network_disconnect(net_stat);
    
    return message;
}

