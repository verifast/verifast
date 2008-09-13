int socket_create_and_listen(int port);
  //@ requires emp;
  //@ ensures emp;

int socket_accept(int serverSocket);
  //@ requires emp;
  //@ ensures emp;

int write(int fd, void *buf, int size);
  //@ requires range(buf, ?bytes) &*& length(bytes) == size;
  //@ ensures range(buf, bytes);

int close(int fd);
  //@ requires emp;
  //@ ensures emp;

int main()
  //@ requires emp;
  //@ ensures emp;
{
    int serverSocket = socket_create_and_listen(12345);

    while (0 == 0)
      //@ invariant emp;
    {
        int slaveSocket = socket_accept(serverSocket);
        char *msg = "Hello, world!";
        write(slaveSocket, msg, 13);
        close(slaveSocket);
    }

    return 0;
}
