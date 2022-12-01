//verifast_options{target:32bit I:../../../crypto_ccs}

#include "dummy_protocol.h"
#include "stdlib.h"

#define APP_RECEIVE_PORT 121212

char get_random_char()
//@ requires true;
//@ ensures true;
{
  return 42;
}

void send()
  //@ requires [?f0]world(dummy_pub, dummy_key_clsfy) &*& principal(?p, ?c); 
  //@ ensures  [f0]world(dummy_pub, dummy_key_clsfy) &*& principal(p, c);
{
    struct network_status *net_stat = 
                                 network_connect("localhost", APP_RECEIVE_PORT);
    
    char i = get_random_char();
    struct item *m = create_data_item_from_int(i);
    //@ assert item(m, ?data, dummy_pub);
    //@ close dummy_pub(data);
    //@ leak dummy_pub(data);
    network_send(net_stat, m);
    item_free(m);
    
    network_disconnect(net_stat);
}

struct item *receive()
  //@ requires [?f0]world(dummy_pub, dummy_key_clsfy) &*& principal(?p, ?c); 
  /*@ ensures  [f0]world(dummy_pub, dummy_key_clsfy) &*& principal(p, c) &*&
               item(result, ?msg, dummy_pub) &*&  msg == data_item(_); @*/
{
    struct network_status *net_stat = network_bind_and_accept(APP_RECEIVE_PORT);
    struct item *m = network_receive(net_stat);
    check_is_data(m);
    network_disconnect(net_stat);
    return m;
}

