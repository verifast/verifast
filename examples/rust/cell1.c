struct cell {
    int x;
};

//@ predicate cell_pred(struct cell *c) = c->x |-> _;

// fun set<'a>(c: &'a cell, v: int)
void set(struct cell *c, int v)
/*@
requires
    foreach(?xs, cell_pred) &*& mem(c, xs) == true;
@*/
/*@
ensures
    foreach(xs, cell_pred);
@*/
{
    //@ foreach_remove(c, xs);
    //@ open cell_pred(c);
    c->x = v;
    //@ close cell_pred(c);
    //@ foreach_unremove(c, xs);
}

// fun do_stuff<'a>(c: &mut 'a)
void do_stuff(struct cell *c)
//@ requires foreach(?xs, cell_pred) &*& cell_pred(c);
//@ ensures foreach(xs, cell_pred) &*& cell_pred(c);
{
    // Start lifetime beta
    // Start immutable borrow of c
    //@ close foreach(cons(c, xs), cell_pred);
    set(c, 10);
    // End lifetime beta; all variables frozen for beta are unfrozen.
    //@ open foreach(cons(c, xs), cell_pred);
}

// fun main()
int main() //@ : custom_main_spec
//@ requires foreach(?xs, cell_pred);
//@ ensures foreach(xs, cell_pred);
{
    struct cell myCell;
    //@ close cell_pred(&myCell);
    do_stuff(&myCell);
    //@ open cell_pred(&myCell);
    return 0;
}