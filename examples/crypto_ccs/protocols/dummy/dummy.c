#include "dummy.h"

#include <stdlib.h>
#include <string.h>

//@ #include "quantifiers.gh"

#define SERVER_PORT 121212

void sender(char* msg)
  /*@ requires principal(?sender, _) &*&
               [?f]chars(msg, PACKAGE_SIZE, ?cs); @*/
  /*@ ensures  principal(sender, _) &*&
               [f]chars(msg, PACKAGE_SIZE, cs); @*/
{
  //@ open principal(sender, _);
  int socket;
  
  net_usleep(20000);
  if(net_connect(&socket, NULL, SERVER_PORT) != 0)
    abort();
  if(net_set_block(socket) != 0)
    abort();
  
  net_send(&socket, msg, PACKAGE_SIZE);
  net_close(socket);
  //@ close principal(sender, _);
}

void receiver(char* msg)
  /*@ requires principal(?receiver, _) &*&
               chars_(msg, PACKAGE_SIZE, _); @*/
  /*@ ensures  principal(receiver, _) &*&
               chars(msg, PACKAGE_SIZE, ?cs); @*/
{
  //@ open principal(receiver, _);
  int socket1;
  int socket2;
  char message[PACKAGE_SIZE];
   
  if(net_bind(&socket1, NULL, SERVER_PORT) != 0)
    abort();
  if(net_accept(socket1, &socket2, NULL) != 0)
    abort();
  if(net_set_block(socket2) != 0)
    abort();
  
  if (net_recv(&socket2, msg, PACKAGE_SIZE) != PACKAGE_SIZE)
    abort();
  net_close(socket1);
  net_close(socket2);
  //@ close principal(receiver, _);
}