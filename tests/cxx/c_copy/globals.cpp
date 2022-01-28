static int x;

struct Counter {
    int f;

    Counter(int f) : f(f)
    //@ requires true;
    //@ ensures this->f |-> f;
    {}
    
    Counter() : f(2)
    //@ requires true;
    //@ ensures this->f |-> 2;
    {}

    ~Counter()
    //@ requires this->f |-> _;
    //@ ensures true;
    {}
};

static Counter *c;

static Counter cc;

void m()
    //@ requires integer(&x, 7) &*& pointer(&c, ?ctr) &*& Counter_f(ctr, ?v) &*& Counter_f(&cc, _);
    //@ ensures integer(&x, 8) &*& pointer(&c, ctr) &*& Counter_f(ctr, v + 1) &*& Counter_f(&cc, 10);
{
    int y = x;
    x = y + 1;
    c->f = c->f + 1;
    cc.f = 10;
}

int main() //@ : main_full(globals)
    //@ requires module(globals, true);
    //@ ensures true;
{
    //@ open_module();
    int x0 = x;

    //@ assert (x0 == 0);
    x = 7;
    Counter *ctr = new Counter(42);
    c = ctr;
    m();
    int ctr_f = ctr->f;
    //@ assert (ctr_f == 43) &*& Counter_f(&cc, 10);

    delete ctr;
    //@ leak integer(&x, _) &*& pointer(&c, _) &*& struct_Counter_padding(&cc) &*& Counter_f(&cc, _);
}