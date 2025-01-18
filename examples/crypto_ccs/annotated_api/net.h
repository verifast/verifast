#ifndef NET_H
#define NET_H

#include "macro_defines.h"

/*@

inductive socket_status =
 | bound_to_port
 | connection_init
 | connected
;

predicate net_status(int socket, list<char> socket_ip, 
                     int socket_port, socket_status socket_stat);

@*/

int net_connect(int *fd, const char *host, int port);
  //@ requires *fd |-> _ &*& [?f]option_string(host, ?s_ip);
  /*@ ensures  integer(fd, ?s_fd) &*& [f]option_string(host, s_ip) &*&
               result == 0 ?
                   net_status(s_fd, s_ip, port, connection_init) 
                 :
                   true; @*/

int net_set_block(int fd);
  //@ requires net_status(fd, ?s_ip, ?port, connection_init);
  /*@ ensures  result == 0 ? 
                 net_status(fd, s_ip, port, connected) 
               : 
                 true; @*/

int net_bind(int *fd, const char *bind_ip, int port);
  //@ requires *fd |-> _ &*& [?f]option_string(bind_ip, ?s_ip);
  /*@ ensures  integer(fd, ?s_fd) &*& [f]option_string(bind_ip, s_ip) &*&
               result == 0 ? 
                 net_status(s_fd, s_ip, port, bound_to_port) 
               : 
                 true; @*/

int net_accept(int bind_fd, int *client_fd, void *client_ip);
  /*@ requires *client_fd |-> _ &*& option_string(client_ip, ?c_ip) &*&
               net_status(bind_fd, ?ip, ?port, bound_to_port); @*/
  /*@ ensures  integer(client_fd, ?c_fd) &*& option_string(client_ip, c_ip) &*& 
               net_status(bind_fd, ip, port, bound_to_port) &*&
               result == 0 ?
                   net_status(c_fd, c_ip, _, connection_init)
                 :
                   true; @*/
  
void net_usleep(unsigned long usec);
  //@ requires true;
  //@ ensures  true;

int net_send(void *ctx, const char *buf, size_t len);
  /*@ requires integer(ctx, ?fd) &*&
               net_status(fd, ?ip, ?port, connected) &*&
               len <= MAX_MESSAGE_SIZE &*&
               [?f1]chars(buf, len, ?cs); @*/
  /*@ ensures  integer(ctx, fd)  &*&
               net_status(fd, ip, port, connected) &*&
               [f1]chars(buf, len, cs); @*/

int net_recv(void *ctx, char *buf, size_t len);
  /*@ requires integer(ctx, ?fd)  &*&
               net_status(fd, ?ip, ?port, connected) &*&
               chars_(buf, len, _) &*& len <= MAX_MESSAGE_SIZE; @*/
  /*@ ensures  integer(ctx, fd)  &*&
               net_status(fd, ip, port, connected) &*&
               result <= len &*&
               chars(buf, max(0, {result}), _) &*& chars_(buf + max(0, {result}), len - max(0, {result}), _); @*/

void net_close(int fd);
  //@ requires net_status(fd, _, _, _);
  //@ ensures  true;

#endif