// This example shows that behavioral subtyping is more flexible than one might expect.

class Cell {

    int value;

    //@ predicate valid(int x) = value |-> x;

    Cell()
        //@ requires true;
        //@ ensures valid(0);
    {
        //@ close valid(0);
    }

    void increment()
        //@ requires valid(?x);
        //@ ensures valid(x + 1);
    {
        //@ open valid(x);
        value++;
        //@ close valid(x + 1);
    }

}

class Recell extends Cell {

    //@ predicate valid(int x) = false &*& x == 0;
    
    void increment()
        //@ requires valid(?x);
        //@ ensures valid(x + 1);
    {
        //@ open valid(x);
        value--; //~allow_dead_code
    }

}