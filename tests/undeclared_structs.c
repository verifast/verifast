typedef struct arraylist *arraylist;

//@ predicate arraylist(arraylist a);

arraylist create_arraylist();
    //@ requires true;
    //@ ensures arraylist(result);

void arraylist_destroy(arraylist a);
    //@ requires arraylist(a);
    //@ ensures true;

int main()
    //@ requires true;
    //@ ensures true;
{
    arraylist a = create_arraylist();
    arraylist_destroy(a);
    unsigned x = sizeof(struct arraylist); //~ should_fail
    return 0;
}
