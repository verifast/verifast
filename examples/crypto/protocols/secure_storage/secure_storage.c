#include "secure_storage.h"
#include "stdlib.h"

#define APP_RECEIVE_PORT 121212

void app_send(struct item *key, struct item *message)
  /*@ requires [?f0]world(ss_pub) &*&
               item(key, key_item(?creator, ?id, 
                                  symmetric_key, int_pair(0, 0))) &*& 
               item(message, ?msg) &*& ss_pub(msg) == true &*& 
               app_send_event(creator, msg) == true; 
  @*/
  /*@ ensures  [f0]world(ss_pub) &*&
               item(key, key_item(creator, id, 
                                  symmetric_key, int_pair(0, 0))) &*& 
               item(message, msg); 
    @*/
{
    struct network_status *net_stat = 
                                 network_connect("localhost", APP_RECEIVE_PORT);
    
    struct item *hash = hmac(key, message);
    struct item *m = create_pair(hash, message);
    network_send(net_stat, m);
    item_free(hash);
    item_free(m);
    
    network_disconnect(net_stat);
}

struct item *app_receive(struct item *key)
  /*@ requires [?f0]world(ss_pub) &*&
               item(key, key_item(?creator, ?id, 
                                  symmetric_key, int_pair(0, 0))); 
  @*/
  /*@ ensures  [f0]world(ss_pub) &*&
               item(key, key_item(creator, id, 
                                  symmetric_key, int_pair(0, 0))) &*& 
               item(result, ?msg) &*& 
               (
                 bad(creator) || 
                 collision_in_run() || 
                 app_send_event(creator, msg)
               );
  @*/
{
    struct network_status *net_stat = network_bind_and_accept(APP_RECEIVE_PORT);
    
    struct item *m = network_receive(net_stat);
    struct item *hash = pair_get_first(m);
    struct item *message = pair_get_second(m);
    item_free(m);
    hmac_verify(hash, key, message);
    item_free(hash);
    
    network_disconnect(net_stat);
    
    return message;
}

