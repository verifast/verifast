#include <stdio.h>   /* */
#include <stdlib.h>  /* exit() */
#include <string.h>  /* memset(), memcpy() */
#include <sys/types.h>
#ifdef WIN32
#include <winsock2.h>
#else
#include <sys/socket.h>   /* socket(), bind(), listen(), accept() */
#include <netinet/in.h>
#include <arpa/inet.h>
#include <netdb.h>
#include <unistd.h>  /* fork(), write(), close() */
#define SOCKET int
#define INVALID_SOCKET (-1)
#endif

#include "socketlib.h"

void print_socket_error_message(char *api)
{
#ifdef WIN32
	printf("Socket API call '%s' failed: error code %d\n", api, WSAGetLastError());
#else
	perror(api);
#endif
}


// Server-side connections
SOCKET socket_create_and_listen(int port)
{
	SOCKET serverSocket = 0;
	struct sockaddr_in serverName = { 0 };
	int status = 0;

#ifdef WIN32
	{
		WSADATA windowsSocketsApiData;
		WSAStartup(MAKEWORD(2, 0), &windowsSocketsApiData);
	}
#endif

	serverSocket = socket(PF_INET, SOCK_STREAM, IPPROTO_TCP);
	if (INVALID_SOCKET == serverSocket)
	{
		print_socket_error_message("socket()");
		abort();
	}

	serverName.sin_addr.s_addr=htonl(INADDR_ANY);
	serverName.sin_family = AF_INET;
	/* network-order */
	serverName.sin_port = htons(port);

	status = bind(serverSocket, (struct sockaddr *) &serverName, sizeof(serverName));
	if (INVALID_SOCKET == status)
	{
		print_socket_error_message("bind()");
		abort();
	}

	status = listen(serverSocket, 5);  // Allow 5 pending incoming connection requests
	if (INVALID_SOCKET == status)
	{
		print_socket_error_message("listen()");
		abort();
	}

	return serverSocket;
}

SOCKET socket_accept(SOCKET serverSocket)
{
	struct sockaddr_in clientName = { 0 };
	SOCKET slaveSocket;
	int clientLength = sizeof(clientName);

	(void) memset(&clientName, 0, sizeof(clientName));

	slaveSocket = accept(serverSocket, (struct sockaddr *) &clientName, &clientLength);
	if (INVALID_SOCKET == slaveSocket)
	{
		print_socket_error_message("accept()");
		abort();
	}

	return slaveSocket;
}


// Client-side connections

SOCKET socket_create(int port)
{
	SOCKET lsocket;
	SOCKADDR_IN lSockAddr;
	SOCKET serverSocket = 0;
	int status = 0;

#ifdef WIN32
	{
		WSADATA windowsSocketsApiData;
		WSAStartup(MAKEWORD(2, 0), &windowsSocketsApiData);
	}
#endif

	lsocket = socket(PF_INET, SOCK_STREAM, IPPROTO_TCP);
	if (INVALID_SOCKET == lsocket)
	{
		print_socket_error_message("socket()");
		abort();
	}

	memset(&lSockAddr,0, sizeof(lSockAddr));
	lSockAddr.sin_family = AF_INET;
	lSockAddr.sin_port = htons(port);
	lSockAddr.sin_addr.s_addr = inet_addr("127.0.0.1");
	status = connect(lsocket,(SOCKADDR *)&lSockAddr,sizeof(SOCKADDR_IN));
	if(status != 0)
	{
		print_socket_error_message("connect()");
		abort();
	}
	return lsocket;
}