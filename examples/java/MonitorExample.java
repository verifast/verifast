import verifast.*;

class Cell
{
    Monitor monitor;
    //@ int min;
    int value;
}

//@ predicate_ctor Cell(Cell c)() = [1/2]c.min |-> ?min &*& c.value |-> ?v &*& 0 <= min &*& min <= v;

class IncrementorCriticalSection implements CriticalSection {

    Cell cell;
    int increment;
    
    //@ predicate pre(predicate() payload) = cell |-> ?c &*& increment |-> ?i &*& 0 <= i &*& payload == Cell(c);
    //@ predicate post() = cell |-> ?c &*& increment |-> _;
    
    public void run()
        //@ requires pre(?payload) &*& payload();
        //@ ensures post() &*& payload();
    {
        //@ open pre(_);
        //@ open Cell(cell)();
        cell.value += increment;
        //@ close Cell(cell)();
        //@ close post();
    }
    
}

class IncrementorThread implements Runnable {

    Cell cell;
    
    IncrementorThread(Cell c)
        //@ requires true;
        //@ ensures cell |-> c;
    { cell = c; }
    
    int pickIncrement()
        //@ requires true;
        //@ ensures 0 <= result;
    {
        return 1;
    }
    
    //@ predicate pre() = cell |-> ?c &*& [_]c.monitor |-> ?m &*& [_]m.Monitor(Cell(c));
    //@ predicate post() = cell |-> ?c &*& [_]c.monitor |-> ?m &*& [_]m.Monitor(Cell(c));
    
    public void run()
        //@ requires pre();
        //@ ensures post();
    {
        for (;;)
            //@ invariant cell |-> ?c &*& [_]c.monitor |-> ?m &*& [_]m.Monitor(Cell(c));
        {
            IncrementorCriticalSection s = new IncrementorCriticalSection();
            s.cell = cell;
            s.increment = pickIncrement();
            cell.monitor.sync(s);
        }
    }
    
}

class ReaderCriticalSection implements CriticalSection {
    
    Cell cell;
    int lastValue;
    
    //@ predicate pre(predicate() payload) = [1/2]cell |-> ?c &*& lastValue |-> ?v &*& [1/2]c.min |-> ?min &*& v <= min &*& payload == Cell(c);
    //@ predicate post() = [1/2]cell |-> ?c &*& lastValue |-> ?v &*& [1/2]c.min |-> v;
    
    public void run()
        //@ requires pre(?payload) &*& payload();
        //@ ensures post() &*& payload();
    {
        //@ open pre(_);
        //@ open Cell(cell)();
        if (cell.value < lastValue)
            assert false;
        lastValue = cell.value;
        //@ cell.min = lastValue;
        //@ close Cell(cell)();
        //@ close post();
    }
    
}

class ReaderThread implements Runnable {

    Cell cell;
    
    //@ predicate pre() = cell |-> ?c &*& [_]c.monitor |-> ?m &*& [_]m.Monitor(Cell(c)) &*& [1/2]c.min |-> ?min &*& 0 <= min;
    //@ predicate post() = true;
    
    ReaderThread(Cell c)
        //@ requires true;
        //@ ensures cell |-> c;
    { cell = c; }
    
    public void run()
        //@ requires pre();
        //@ ensures post();
    {
        //@ open pre();
        ReaderCriticalSection s = new ReaderCriticalSection();
        s.cell = cell;
        s.lastValue = Integer.MIN_VALUE;
        
        for (;;)
            //@ invariant cell |-> ?c &*& [_]c.monitor |-> ?m &*& [_]m.Monitor(Cell(c)) &*& s.cell |-> c &*& s.lastValue |-> ?v &*& [1/2]c.min |-> ?min &*& v <= min;
        {
            //@ close s.pre(Cell(c));
            cell.monitor.sync(s);
            //@ open s.post();
        }
        //@ close post();
    }
    
}

public class MonitorExample {
    
    public static void main(String[] args)
        //@ requires true;
        //@ ensures true;
    {
        Cell cell = new Cell();
        //@ close exists(Cell(cell));
        //@ close Cell(cell)();
        cell.monitor = new Monitor();
        //@ leak cell.monitor |-> ?m &*& m.Monitor(_);
        new Thread(new ReaderThread(cell)).start();
        new Thread(new IncrementorThread(cell)).start();
    }
    
}