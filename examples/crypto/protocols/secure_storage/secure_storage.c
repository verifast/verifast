#include "secure_storage.h"
#include "stdlib.h"

#define APP_RECEIVE_PORT 121212

/*@ 
predicate protocol_pub(; fixpoint(item, bool) pub) = pub == ss_pub;

lemma void init_protocol()
     requires true;
     ensures protocol_pub(ss_pub);
{
  close protocol_pub(ss_pub);
}
@*/

void app_send(struct item *key, struct item *message)
  /*@ requires [?f0]world(ss_pub) &*& [?f1]net_api_initialized() &*&
                key_item(key, ?creator, ?id, symmetric_key, int_pair(0, 0)) &*& 
                item(message, ?msg) &*& ss_pub(msg) == true &*& 
                app_send_event(creator, msg) == true; 
  @*/
  /*@ ensures  [f0]world(ss_pub) &*& [f1]net_api_initialized() &*&
                key_item(key, creator, id, symmetric_key, int_pair(0, 0)) &*& 
                item(message, msg); 
    @*/
{
    struct network_status *net_stat = 
                                 network_connect("localhost", APP_RECEIVE_PORT);
    
    struct item *hash = hmac(key, message);
    struct item *m = create_pair(hash, message);
    item_free(hash);
    network_send(net_stat, m);
    item_free(m);
    
    network_disconnect(net_stat);
}

struct item *app_receive(struct item *key)
  /*@ requires [?f0]world(ss_pub) &*& [?f1]net_api_initialized() &*&
                key_item(key, ?creator, ?id, symmetric_key, int_pair(0, 0)); 
  @*/
  /*@ ensures [f0]world(ss_pub) &*& [f1]net_api_initialized() &*&
              key_item(key, creator, id, symmetric_key, int_pair(0, 0)) &*& 
              item(result, ?msg) &*& bad(creator) || 
              app_send_event(creator, msg); 
  @*/
{
    struct network_status *net_stat = network_bind(APP_RECEIVE_PORT);
    
    struct item *m = network_receive(net_stat);
    struct item *hash = pair_get_first(m);
    struct item *message = pair_get_second(m);
    item_free(m);
    hmacsha1_verify(hash, key, message);
    item_free(hash);
    
    network_disconnect(net_stat);
    
    return message;
}

