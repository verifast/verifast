#include "network.h"

#include "item.h"
#include "serialization.h"
#include "deserialization.h"
#include "general.h"
#include "principal_ids.h"

#define TIME_BOUND 0x3fffffff

/*@

predicate network_status_core(struct network_status *stat, bool initialized) =
  stat !=  0 &*&
  malloc_block_network_status(stat) &*&
  network_status_initialized(stat, ?i) &*&
    (i == 0 || i == 1) &*& 
    initialized == (i == 1) &*&
  stat->listen_socket |-> ?l_socket &*&
    (l_socket == -1 ? true : initialized == true &*&
        net_status(l_socket, nil, ?l_port, bound_to_port)
    ) &*&
  stat->client_socket |-> ?c_socket &*&
    (c_socket == -1 ? true : initialized == true &*&
       net_status(c_socket, ?c_ip, ?c_port, connected)
    ) &*&
  stat->server_socket |-> ?s_socket &*&
    (s_socket == -1 ? true : initialized == true &*&
       net_status(s_socket, ?s_ip, ?s_port, connected)
    )
;

predicate network_status(struct network_status *stat) =
  network_status_core(stat, true)
;

@*/


struct network_status
{
  int initialized;

  int listen_socket;
  int client_socket;
  int server_socket;
};

void network_sleep(unsigned int microseconds)
  //@ requires true;
  //@ ensures  true;
{
  net_usleep(microseconds);
}

struct network_status *network_status_uninitialized()
  //@ requires true;
  //@ ensures  network_status_core(result, false);
{
  struct network_status *stat = malloc(sizeof(struct network_status));
  if (stat == 0) {abort_crypto_lib("Network status could not be initialized");}
  
  stat->listen_socket = -1;
  stat->client_socket = -1;
  stat->server_socket = -1;
  stat->initialized = 0;

  //@ close network_status_core(stat, false);
  return stat;
}

struct network_status *network_connect(const char *name, int port)
  //@ requires [?f1]option_string(name, ?ip);
  //@ ensures  [f1]option_string(name, ip) &*& network_status(result);
{
  struct network_status *stat = network_status_uninitialized();
  
  int time = 10;
  int i;
  for (i = 0; i < 50; i++)
    /*@ invariant network_status_core(stat, false) &*&
                  time > 0 &*& time < TIME_BOUND &*&
                  [f1]option_string(name, ip); @*/
  {
    //@ open network_status_core(stat, false);
    if (net_connect(&stat->server_socket, name, port) == 0)
    {
      if (net_set_block(stat->server_socket) == 0)
      {
        if(stat->server_socket == -1)
          abort_crypto_lib("Got a negative file descriptor");

        stat->initialized = 1;
        //@ close network_status_core(stat, true);
        //@ close network_status(stat);
        return stat;
      }
      else
        break;
    }
    stat->server_socket = -1;
    //@ close network_status_core(stat, false);
    
    if (time * 2 < TIME_BOUND)
      time = time * 2;
    else
      break;
      
    network_sleep((unsigned int) time);
  }
  
  abort_crypto_lib("Failed to connect to server");
}

struct network_status *network_bind_and_accept(int port)
  //@ requires true;
  //@ ensures  network_status(result);
{
  struct network_status *stat = network_bind(port);
  network_accept(stat);
  //@ close network_status(stat);
  return stat;
}

struct network_status *network_bind(int port)
  //@ requires true;
  //@ ensures  network_status_core(result, true);
{ 
  int time = 10;
  int i;
  for (i = 0; i < 50; i++)
    //@ invariant time > 0 &*& time < TIME_BOUND;
  {
    struct network_status *stat = network_status_uninitialized();
    //@ open network_status_core(stat, false);
    
    //@ close chars(NULL, 0, nil);
    if (net_bind(&stat->listen_socket, NULL, port) == 0)
    {
      if (stat->listen_socket != -1)
      {
        stat->initialized = 1;
        //@ close network_status_core(stat, true);
        return stat;
      }
      
      net_close(stat->listen_socket);
    }
    
    free(stat);
    if (time * 2 < TIME_BOUND)
      time = time * 2;
    else
      break;
    
    network_sleep((unsigned int) time);
  }
  
  abort_crypto_lib("Failed to bind to port");
}

void network_accept(struct network_status *stat)
  //@ requires network_status_core(stat, true);
  //@ ensures  network_status_core(stat, true);
{
  //@ open network_status_core(stat, true);
  if (stat->listen_socket > 0 && stat->client_socket == -1)
  {
    //@ close chars(NULL, 0, nil);
    if(net_accept(stat->listen_socket, &stat->client_socket, NULL) != 0)
      abort_crypto_lib("Failed to accept client");
    if(stat->client_socket == -1)
      abort_crypto_lib("Got a negative file descriptor");
    
    if (net_set_block(stat->client_socket) == 0)
    {
      stat->initialized = 1;
    }
    else
      abort_crypto_lib("Failed to open client connection");
  }
  //@ close network_status_core(stat, true);
}

void network_disconnect(struct network_status *stat)
  //@ requires network_status(stat);
  //@ ensures  true;
{
  //@ open network_status(stat);
  //@ open network_status_core(stat, true);    

  if (stat->client_socket != -1)
    net_close(stat->client_socket);

  if (stat->listen_socket != -1)
    net_close(stat->listen_socket);

  if (stat->server_socket != -1)
    net_close(stat->server_socket);

  free(stat);
}

void network_send(struct network_status *stat, struct item* datagram)
  /*@ requires [?f]world(?pub, ?key_clsfy) &*& network_status(stat) &*&
               item(datagram, ?d, pub) &*& [_]pub(d); @*/
  /*@ ensures  [f]world(pub, key_clsfy) &*& network_status(stat) &*&
               item(datagram, d, pub); @*/
{
  int socket = -1;
  
  debug_print("network_send");
  print_item(datagram);
  
  //@ open network_status(stat);
  //@ open network_status_core(stat, true);
  if (stat->listen_socket > 0 && stat->client_socket > 0)
    socket = stat->client_socket;
  else if (stat->server_socket > 0)
    socket = stat->server_socket;
  
  if (socket > 0)
  {
    char* message;
    int size = serialize_to_public_message(&message, datagram);
    if (size > MAX_PACKAGE_SIZE)
       abort_crypto_lib("Message to send is to big");

    net_send(&socket, message, (unsigned int) size);
    free(message);
  }
  //@ close network_status_core(stat, true);
  //@ close network_status(stat);  
}

struct item *network_receive_attempt(struct network_status *stat)
  /*@ requires [?f0]world(?pub, ?key_clsfy) &*& network_status(stat) &*&
               proof_obligations(pub); @*/
  /*@ ensures  [f0]world(pub, key_clsfy) &*& network_status(stat) &*&
               proof_obligations(pub) &*&
               result == 0 ? 
                 true 
               : 
                 item(result, ?d, pub) &*& [_]pub(d); @*/
{
  int socket = -1;
  struct item *result = 0;
  
  //@ open network_status(stat);
  //@ open network_status_core(stat, true);
  if (stat->listen_socket > 0 && stat->client_socket > 0)
    socket = stat->client_socket;
  else if (stat->server_socket > 0)
    socket = stat->server_socket;
  
  if (socket > 0)
  {
    char receive_buffer[MAX_PACKAGE_SIZE];
    int received = net_recv(&socket, receive_buffer, MAX_PACKAGE_SIZE);
    //receiving failed?
    if (received > 0)
    {
      debug_print("network_receive");
      //@ chars_to_crypto_chars(receive_buffer, received);
      print_buffer(receive_buffer, received);
      //@ crypto_chars_to_chars(receive_buffer, received);
      result = deserialize(receive_buffer, received);
    }
  }
  
  //@ close network_status_core(stat, true);
  //@ close network_status(stat);
  return result;
}

struct item *network_receive(struct network_status *stat)
  /*@ requires [?f]world(?pub, ?key_clsfy) &*& network_status(stat); @*/
  /*@ ensures  [f]world(pub, key_clsfy) &*& network_status(stat) &*&
               item(result, ?d, pub) &*& [_]pub(d); @*/
{
  //@ retreive_proof_obligations();
  struct item *i = network_receive_attempt(stat);
  if (i == 0)
    abort_crypto_lib("Receiving message failed");

  return i;
  //@ leak proof_obligations(pub);
}
