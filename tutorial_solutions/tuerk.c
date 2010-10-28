char getchar();
    //@ requires true;
    //@ ensures true;
void putchar(char c);
    //@ requires true;
    //@ ensures true;

/*@
predicate characters(char *start, int count) =
    count <= 0 ? true : character(start, _) &*& characters(start + 1, count - 1);
@*/

char *malloc(int count);
    //@ requires true;
    //@ ensures characters(result, count);

void getchars(char *start, int count)
    //@ requires characters(start, count);
    //@ ensures characters(start, count);
{
    int i = 0;
    while (i < count)
        //@ requires characters(start + i, count - i);
        //@ ensures characters(start + old_i, count - old_i);
    {
        //@ open characters(start + i, count - i);
        char c = getchar();
        *(start + i) = c;
        i++;
        //@ recursive_call();
        //@ close characters(start + old_i, count - old_i);
    }
}

void putchars(char *start, int count)
    //@ requires characters(start, count);
    //@ ensures characters(start, count);
{
    int i = 0;
    while (i < count)
        //@ requires characters(start + i, count - i);
        //@ ensures characters(start + old_i, count - old_i);
    {
        //@ open characters(start + i, count - i);
        putchar(*(start + i));
        i++;
        //@ recursive_call();
        //@ close characters(start + old_i, count - old_i);
    }
}

int main()
    //@ requires true;
    //@ ensures true;
{
    char *array = malloc(100);
    getchars(array, 100);
    putchars(array, 100);
    putchars(array, 100);
    //@ leak characters(array, 100);
    return 0;
}
