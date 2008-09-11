#include <stdio.h>   /* */
#include <stdlib.h>  /* exit() */
#include <string.h>  /* memset(), memcpy() */
#include <sys/utsname.h>   /* uname() */
#include <sys/types.h>
#include <sys/socket.h>   /* socket(), bind(), listen(), accept() */
#include <netinet/in.h>
#include <arpa/inet.h>
#include <netdb.h>
#include <unistd.h>  /* fork(), write(), close() */

int socket_create_and_listen(int port)
  //@ requires emp;
  //@ ensures emp;
{
    int serverSocket = 0;
    struct sockaddr_in serverName = { 0 };
    int status = 0;

    serverSocket = socket(PF_INET, SOCK_STREAM, IPPROTO_TCP);
    if (-1 == serverSocket)
    {
        perror("socket()");
        exit(1);
    }
    
    serverName.sin_addr.s_addr=htonl(INADDR_ANY);
    serverName.sin_family = AF_INET;
    /* network-order */
    serverName.sin_port = htons(port);

    status = bind(serverSocket, (struct sockaddr *) &serverName, sizeof(serverName));
    if (-1 == status)
    {
        perror("bind()");
        exit(1);
    }
    
    status = listen(serverSocket, 5);  // Allow 5 pending incoming connection requests
    if (-1 == status)
    {
        perror("listen()");
        exit(1);
    }

    return serverSocket;
}

int socket_accept(int serverSocket)
  //@ requires emp;
  //@ ensures emp;
{
    struct sockaddr_in clientName = { 0 };
    int slaveSocket, clientLength = sizeof(clientName);

    (void) memset(&clientName, 0, sizeof(clientName));

    slaveSocket = accept(serverSocket, (struct sockaddr *) &clientName, &clientLength);
    if (-1 == slaveSocket)
    {
        perror("accept()");
        exit(1);
    }
    
    return slaveSocket;
}
