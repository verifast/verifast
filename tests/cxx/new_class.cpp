/*@
predicate EmptyPred(struct Empty *e) =
    new_block_Empty(e);
@*/
class Empty {};

/*@
predicate FieldsPred(struct Fields *f, int i, bool b, struct Empty *e) =
    new_block_Fields(f) &*& f->i |-> i &*& f->b |-> b &*& f->e |-> e &*& EmptyPred(e);
@*/
struct Fields {
    int i = 0;
    bool b = false;
    Empty *e = nullptr;
};

int main() 
//@ requires true;
//@ ensures true;
{
    Empty *e = new Empty;
    //@ close EmptyPred(e);
    Fields *f = new Fields;
    f->e = e;
    //@ close FieldsPred(f, 0, false, e);
    //@ open FieldsPred(f, ?i, ?b, e);
    f->i += 1;
    //@ assert(f->i == i + 1);
    //@ close FieldsPred(f, i+1, b, e);
    
    //@ leak FieldsPred(_, _, _, _);
}