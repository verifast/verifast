#include "network.h"

#include "item.h"
#include "serialization.h"
#include "general.h"
#include "principals.h"

#define TIME_BOUND 0x3fffffff

/*@

predicate network_status_core(struct network_status *stat, bool initialized) =
  stat !=  0 &*&
  malloc_block_network_status(stat) &*&
  network_status_initialized(stat, ?i) &*&
    (i == 0 || i == 1) &*& 
    initialized == (i == 1) &*&
  network_status_listen_socket(stat, ?l_socket) &*&
    (l_socket == -1 ? true : initialized == true &*&
        polarssl_net_status(l_socket, nil, ?l_port, bound_to_port)
    ) &*&
  network_status_client_socket(stat, ?c_socket) &*&
    (c_socket == -1 ? true : initialized == true &*&
       polarssl_net_status(c_socket, ?c_ip, ?c_port, connected)
    ) &*&
  network_status_server_socket(stat, ?s_socket) &*&
    (s_socket == -1 ? true : initialized == true &*&
       polarssl_net_status(s_socket, ?s_ip, ?s_port, connected)
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
  //@ requires [?f0]world(?pub);
  //@ ensures  [f0]world(pub);
{
  //@ open [f0]world(pub);
  net_usleep(microseconds);
  //@ close [f0]world(pub);
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
  /*@ requires [?f0]world(?pub) &*&
               [?f1]string(name, ?cs); @*/
  /*@ ensures  [f0]world(pub) &*&
               [f1]string(name, cs) &*& network_status(result); @*/
{
  struct network_status *stat = network_status_uninitialized();
  
  int time = 10;
  for (int i = 0; i < 50; i++)
    /*@ invariant [f0]world(pub) &*& network_status_core(stat, false) &*&
                  time > 0 &*& time < TIME_BOUND &*&
                  [f1]string(name, cs); @*/
  {
    //@ open [f0]world(pub);
    
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

        //@ close [f0]world(pub);
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

    //@ close [f0]world(pub);
    network_sleep((unsigned int) time);
  }
  
  abort_crypto_lib("Failed to connect to server");
  return 0;
}

struct network_status *network_bind_and_accept(int port)
  //@ requires [?f0]world(?pub);
  //@ ensures  [f0]world(pub) &*& network_status(result);
{
  struct network_status *stat = network_bind(port);
  network_accept(stat);
  //@ close network_status(stat);
  return stat;
}

struct network_status *network_bind(int port)
  //@ requires [?f0]world(?pub);
  //@ ensures  [f0]world(pub) &*& network_status_core(result, true);
{ 
  int time = 10;
  for (int i = 0; i < 50; i++)
    /*@ invariant [f0]world(pub) &*&
                  time > 0 &*& time < TIME_BOUND; @*/
  {
    //@ open [f0]world(pub);
    struct network_status *stat = network_status_uninitialized();
    //@ open network_status_core(stat, false);
    
    //@ close chars(NULL, 0, nil);
    if (net_bind(&stat->listen_socket, NULL, port) == 0)
    {
      if (stat->listen_socket != -1)
      {
        stat->initialized = 1;
        //@ close network_status_core(stat, true);
        //@ close [f0]world(pub);
        return stat;
      }
      
      net_close(stat->listen_socket);
    }
    
    free(stat);
    if (time * 2 < TIME_BOUND)
      time = time * 2;
    else
      break;
    
    //@ close [f0]world(pub);
    network_sleep((unsigned int) time);
  }
  
  abort_crypto_lib("Failed to bind to port");
  return 0;
}

void network_accept(struct network_status *stat)
  //@ requires [?f0]world(?pub) &*& network_status_core(stat, true);
  //@ ensures  [f0]world(pub) &*& network_status_core(stat, true);
{
  //@ open network_status_core(stat, true);
  if (stat->listen_socket > 0 && stat->client_socket == -1)
  {
    //@ open [f0]world(pub);
    //@ close chars(NULL, 0, nil);
    if(net_accept(stat->listen_socket, &stat->client_socket, NULL) != 0)
      abort_crypto_lib("Failed to accept client");
    if(stat->client_socket == -1)
      abort_crypto_lib("Got a negative file descriptor");
    
    if (net_set_block(stat->client_socket) == 0)
    {
      stat->initialized = 1;
      //@ close [f0]world(pub);
    }
    else
      abort_crypto_lib("Failed to open client connection");
  }
  //@ close network_status_core(stat, true);
}

void network_disconnect(struct network_status *stat)
  //@ requires [?f0]world(?pub) &*& network_status(stat);
  //@ ensures  [f0]world(pub);
{
  //@ open [f0]world(pub);
  //@ open network_status(stat);
  //@ open network_status_core(stat, true);    

  if (stat->client_socket != -1)
    net_close(stat->client_socket);

  if (stat->listen_socket != -1)
    net_close(stat->listen_socket);

  if (stat->server_socket != -1)
    net_close(stat->server_socket);

  free(stat);
  //@ close [f0]world(pub);
}

void network_send(struct network_status *stat, struct item* datagram)
  /*@ requires [?f0]world(?pub) &*& network_status(stat) &*&
               item(datagram, ?d) &*& (collision_in_run() || pub(d)); @*/
  /*@ ensures  [f0]world(pub) &*& network_status(stat) &*&
               item(datagram, d); @*/
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
    char* message = 0;
    int message_size = 0;
    
    int temp = item_serialize(&message, datagram);
    message_size = temp;
    if (message_size > MAX_PACKAGE_SIZE)
      abort_crypto_lib("Message to send is to big");

    //@ open [f0]world(pub);
    //@ close polarssl_witness<item>(d);
    net_send(&socket, message, (unsigned int) message_size);
    //@ close [f0]world(pub);
    free(message);
  }
  //@ close network_status_core(stat, true);
  //@ close network_status(stat);  
}

struct item *network_receive_attempt(struct network_status *stat)
  //@ requires [?f0]world(?pub) &*& network_status(stat);
  /*@ ensures  [f0]world(pub) &*& network_status(stat) &*&
               result == 0 ? true : item(result, ?d) &*& 
               (collision_in_run() || pub(d)); @*/
{
  int socket = -1;
  struct item *result = 0;
  debug_print("network_receive");
  
  //@ open network_status(stat);
  //@ open network_status_core(stat, true);
  if (stat->listen_socket > 0 && stat->client_socket > 0)
    socket = stat->client_socket;
  else if (stat->server_socket > 0)
    socket = stat->server_socket;
  
  if (socket > 0)
  {
    char receive_buffer[MAX_PACKAGE_SIZE];
    //@ open [f0]world(pub);
    int received = net_recv(&socket, receive_buffer, MAX_PACKAGE_SIZE);
    //@ close [f0]world(pub);
    
    //receiving failed?
    if (received >= 0)
    {      
      //@ assert chars(receive_buffer, received, ?cs);
      //@ open polarssl_witness<item>(?witness);
      //@ close deserialization_attempt(witness, cs);
      result = item_deserialize(receive_buffer, received);
      /*@ if (collision_in_run())
          {
            assert item(result, _);
          }
          else
          {
            assert item(result, witness);
          }
      @*/
    }
  }
  
  //@ close network_status_core(stat, true);
  //@ close network_status(stat);
  return result;
}

struct item *network_receive(struct network_status *stat)
  //@ requires [?f0]world(?pub) &*& network_status(stat);
  /*@ ensures  [f0]world(pub) &*& network_status(stat) &*&
               item(result, ?d) &*& (collision_in_run() || pub(d)); @*/
{
  struct item *i = network_receive_attempt(stat);
  if (i == 0)
    abort_crypto_lib("Receiving message failed");

  return i;
}


