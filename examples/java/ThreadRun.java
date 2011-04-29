//@ predicate started(Thread t);

class Thread {

    //@ predicate pre() = true;
    //@ predicate post() = true;

    Thread()
        //@ requires true;
        //@ ensures true;
    {
    }

    void start()
        //@ requires this.pre();
        //@ exsures true;
        //@ ensures started(this);
    {
        throw null;
    }

    void run()
        //@ requires pre();
        //@ ensures post();
    {
        //@ open pre();
        //@ close post();
    }

    void join()
        //@ requires started(this);
        //@ exsures true;
        //@ ensures this.post();
    {
        throw null;
    }

}

class MyThread extends Thread {

    int x;

    MyThread()
        //@ requires true;
        //@ ensures pre();
    {
        //@ close pre();
    }

    //@ predicate pre() = x |-> 0;
    //@ predicate post() = x |-> 1;

    void run()
        //@ requires pre();
        //@ ensures post();
    {
        //@ open pre();
        x++;
        //@ close post();
    }

    int getResult()
        //@ requires post();
        //@ ensures x |-> 1 &*& result == 1;
    {
        //@ open post();
        return x;
    }
}

class Program {

    public static void main(String[] args)
        //@ requires true;
        //@ exsures true;
        //@ ensures true;
    {
        MyThread t = new MyThread();
        t.start();
        t.join();
        int result = t.getResult();
        assert result == 1;
    }

}
