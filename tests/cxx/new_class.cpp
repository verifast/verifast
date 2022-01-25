/*@
predicate EmptyPred(struct Empty *e) = 
    e != 0;
@*/
class Empty {
public:
    Empty()
    //@ requires true;
    //@ ensures EmptyPred(this);
    {
        //@ close EmptyPred(this);
    }
    
    ~Empty()
    //@ requires EmptyPred(this);
    //@ ensures true;
    {
        //@ open EmptyPred(this);
    }
};

/*@
predicate FieldsPred(struct Fields *f, int i, bool b, struct Empty *e) =
    f->i |-> i &*& f->b |-> b &*& f->e |-> e &*& (e == 0 ? true : (new_block_Empty(e) &*& EmptyPred(e)));
@*/
struct Fields {
    int i = 0;
    bool b = false;
    Empty *e = nullptr;

    Fields()
    //@ requires true;
    //@ ensures FieldsPred(this, 0, false, 0);
    {
        //@ close FieldsPred(this, _, _, _);
    }
    
    ~Fields()
    //@ requires FieldsPred(this, _, _, _);
    //@ ensures true;
    {
        //@ open FieldsPred(this, _, _, _);
        if (e) {
            delete e;
        }
    }
};

int main() 
//@ requires true;
//@ ensures true;
{
    Empty *e = new Empty;
    Fields *f = new Fields;
    //@ open FieldsPred(f, _, _, _);
    f->e = e;
    //@ close FieldsPred(f, 0, false, e);
    //@ open FieldsPred(f, ?i, ?b, e);
    f->i += 1;
    //@ assert(f->i == i + 1);
    //@ close FieldsPred(f, i+1, b, e);
    
    //@ leak FieldsPred(f, _, _, _);
    //@ leak new_block_Fields(f);
}