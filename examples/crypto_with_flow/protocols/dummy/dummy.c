#include "dummy.h"

#include <stdlib.h>
#include <string.h>

//@ #include "quantifiers.gh"

#define SERVER_PORT 121212

void sender()
  //@ requires true;
  //@ ensures  true;

{
  int socket;
  char message[PACKAGE_SIZE];
  
  net_usleep(20000);
  if(net_connect(&socket, NULL, SERVER_PORT) != 0)
    abort();
  if(net_set_block(socket) != 0)
    abort();
  
  net_send(&socket, message, PACKAGE_SIZE);
  net_close(socket);
}

void receiver()
  //@ requires true;
  //@ ensures  true;
{
  int socket1;
  int socket2;
  char message[PACKAGE_SIZE];
   
  if(net_bind(&socket1, NULL, SERVER_PORT) != 0)
    abort();
  if(net_accept(socket1, &socket2, NULL) != 0)
    abort();
  if(net_set_block(socket2) != 0)
    abort();
  
  net_recv(&socket2, message, PACKAGE_SIZE);
  net_close(socket1);
  net_close(socket2);
}