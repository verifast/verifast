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

int main(int argc, char *argv[])
{
    int port = 0;
    int serverSocket = 0;
    struct sockaddr_in serverName = { 0 };
    int status = 0;

    port = 12345;

    serverSocket = socket(PF_INET, SOCK_STREAM, IPPROTO_TCP);
    if (-1 == serverSocket)
    {
        perror("socket()"); // Print the error message for errno
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

    for (;;)
    {
        struct sockaddr_in clientName = { 0 };
        int slaveSocket, clientLength = sizeof(clientName);
        char * msg = "Hello world!";

        (void) memset(&clientName, 0, sizeof(clientName));

        slaveSocket = accept(serverSocket, (struct sockaddr *) &clientName, &clientLength);
        if (-1 == slaveSocket)
        {
            perror("accept()");
            exit(1);
        }

        write(slaveSocket, msg, strlen(msg));
        close(slaveSocket);
    }

    return 0;
}
