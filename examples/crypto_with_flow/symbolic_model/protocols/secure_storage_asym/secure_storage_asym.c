#include "secure_storage_asym.h"
#include "stdlib.h"

#define APP_RECEIVE_PORT 191919

void app_send(struct item *KA_PRIVATE, struct item *message)
  /*@ requires [?f0]world(ss_auth_pub, ss_auth_key_clsfy) &*&
               principal(?principal, ?count) &*&
               item(KA_PRIVATE, ?kap, ss_auth_pub) &*& 
                 kap == private_key_item(?sender, ?count_kap) &*&
               item(message, ?msg, ss_auth_pub) &*&
                 [_]ss_auth_pub(msg) &*& 
                 app_send_event(sender, msg) == true; @*/
  /*@ ensures  [f0]world(ss_auth_pub, ss_auth_key_clsfy) &*&
               principal(principal, count + 1) &*&
               item(KA_PRIVATE, kap, ss_auth_pub) &*& 
               item(message, msg, ss_auth_pub); @*/
{
    struct network_status *net_stat = 
                                 network_connect("localhost", APP_RECEIVE_PORT);
    
    struct item *sign = asymmetric_signature(KA_PRIVATE, message);
    //@ assert item(sign, ?h, ss_auth_pub);
    //@ close ss_auth_pub(h);
    //@ leak ss_auth_pub(h);
    struct item *m = create_pair(sign, message);
    //@ assert item(m, ?pmessage, ss_auth_pub);
    //@ close ss_auth_pub(pmessage);
    //@ leak ss_auth_pub(pmessage);
    network_send(net_stat, m);
    item_free(sign);
    item_free(m);
    
    network_disconnect(net_stat);
}

struct item *app_receive(struct item *KA)
  /*@ requires [?f0]world(ss_auth_pub, ss_auth_key_clsfy) &*&
               principal(?principal, ?count) &*&
               item(KA, ?ka, ss_auth_pub) &*&
                 ka == public_key_item(?sender, ?count_kap); @*/
  /*@ ensures  [f0]world(ss_auth_pub, ss_auth_key_clsfy) &*&
               principal(principal, count) &*&
               item(KA, ka, ss_auth_pub) &*&
               item(result, ?msg, ss_auth_pub) &*&
               col || bad(sender) || app_send_event(sender, msg); @*/
{
    struct network_status *net_stat = network_bind_and_accept(APP_RECEIVE_PORT);
    
    struct item *m = network_receive(net_stat);
    struct item *sign = pair_get_first(m);
    struct item *message = pair_get_second(m);
    //@ assert item(m, pair_item(?hmac_i, ?message_i), ss_auth_pub);
    //@ open [_]ss_auth_pub(pair_item(hmac_i, message_i));
    //@ if (!col) open [_]ss_auth_pub(hmac_i);
    //@ if (!col) open [_]ss_auth_pub(message_i);
    item_free(m);
    check_is_asymmetric_signature(sign);
    asymmetric_signature_verify(KA, message, sign);
    item_free(sign);
    
    network_disconnect(net_stat);
    
    return message;
}
