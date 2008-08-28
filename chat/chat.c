/*
 * Listing 1:
 * Simple "Hello, World!" server
 * Ivan Griffin (ivan.griffin@ul.ie)
 */

#include <stdio.h>   /* */
#include <stdlib.h>  /* exit() */
#include <string.h>  /* memset(), memcpy() */
#include <sys/utsname.h>   /* uname() */
#include <sys/types.h>
#include <sys/socket.h>   /* socket(), bind(),
                             listen(), accept() */
#include <netinet/in.h>
#include <arpa/inet.h>
#include <netdb.h>
#include <unistd.h>  /* fork(), write(), close() */

/*
 * prototypes
 */
int _GetHostName(char *buffer, int length);

/*
 * constants
 */
const char MESSAGE[] = "Hello, World!\n";
const int BACK_LOG = 5;

int main(int argc, char *argv[])
{
    int serverSocket = 0,
        on = 0,
        port = 0,
        status = 0,
        childPid = 0;
    struct hostent *hostPtr = NULL;
    char hostname[80] = "";
    struct sockaddr_in serverName = { 0 };

    if (2 != argc)
    {
        fprintf(stderr, "Usage: %s <port>\n",
      argv[0]);
        exit(1);
    }
    port = atoi(argv[1]);

    serverSocket = socket(PF_INET, SOCK_STREAM,
      IPPROTO_TCP);
    if (-1 == serverSocket)
    {
        perror("socket()");
        exit(1);
    }

    /*
     * turn off bind address checking, and allow
     * port numbers to be reused - otherwise
     * the TIME_WAIT phenomenon will prevent
     * binding to these address.port combinations
     * for (2 * MSL) seconds.
     */

    on = 1;

    status = setsockopt(serverSocket, SOL_SOCKET,
      SO_REUSEADDR,
        (const char *) &on, sizeof(on));

    if (-1 == status)
    {
        perror("setsockopt(...,SO_REUSEADDR,...)");
    }

    /*
     * when connection is closed, there is a need
     * to linger to ensure all data is
     * transmitted, so turn this on also
     */
    {
        struct linger linger = { 0 };

        linger.l_onoff = 1;
        linger.l_linger = 30;
        status = setsockopt(serverSocket,
      SOL_SOCKET, SO_LINGER,
      (const char *) &linger,
      sizeof(linger));

        if (-1 == status)
        {
            perror("setsockopt(...,SO_LINGER,...)");
        }
    }

    /*
     * find out who I am
     */

    status = _GetHostName(hostname,
      sizeof(hostname));
    if (-1 == status)
    {
        perror("_GetHostName()");
        exit(1);
    }

    hostPtr = gethostbyname(hostname);
    if (NULL == hostPtr)
    {
        perror("gethostbyname()");
        exit(1);
    }

    (void) memset(&serverName, 0,
      sizeof(serverName));
    (void) memcpy(&serverName.sin_addr,
      hostPtr->h_addr,
      hostPtr->h_length);

/*
 * to allow server be contactable on any of
 * its IP addresses, uncomment the following
 * line of code:
 * serverName.sin_addr.s_addr=htonl(INADDR_ANY);
 */

    serverName.sin_family = AF_INET;
    /* network-order */
    serverName.sin_port = htons(port);

    status = bind(serverSocket,
   (struct sockaddr *) &serverName,
        sizeof(serverName));
    if (-1 == status)
    {
        perror("bind()");
        exit(1);
    }

    status = listen(serverSocket, BACK_LOG);
    if (-1 == status)
    {
        perror("listen()");
        exit(1);
    }

    for (;;)
    {
        struct sockaddr_in clientName = { 0 };
        int slaveSocket, clientLength =
      sizeof(clientName);

        (void) memset(&clientName, 0,
      sizeof(clientName));

        slaveSocket = accept(serverSocket,
      (struct sockaddr *) &clientName,
      &clientLength);
        if (-1 == slaveSocket)
        {
            perror("accept()");
            exit(1);
        }

        childPid = fork();

        switch (childPid)
        {
        case -1: /* ERROR */
            perror("fork()");
            exit(1);

        case 0: /* child process */

            close(serverSocket);

            if (-1 == getpeername(slaveSocket,
      (struct sockaddr *) &clientName,
      &clientLength))
            {
                perror("getpeername()");
            }
            else
            {
            printf("Connection request from %s\n",
                    inet_ntoa(clientName.sin_addr));
            }

            /*
             * Server application specific code
             * goes here, e.g. perform some
             * action, respond to client etc.
             */
            write(slaveSocket, MESSAGE,
         strlen(MESSAGE));
            close(slaveSocket);
            exit(0);

        default: /* parent process */
            close(slaveSocket);
        }
    }

    return 0;
}

/*
 * Local replacement of gethostname() to aid
 * portability */
int _GetHostName(char *buffer, int length)
{
    struct utsname sysname = { 0 };
    int status = 0;

    status = uname(&sysname);
    if (-1 != status)
    {
        strncpy(buffer, sysname.nodename, length);
    }

    return (status);
}

