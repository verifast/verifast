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
    if (count > 0) {
        //@ open characters(start, count);
        char c = getchar();
        *start = c;
        getchars(start + 1, count - 1);
        //@ close characters(start, count);
    }
}

void xorchars(char *text, char *key, int count)
    //@ requires characters(text, count) &*& characters(key, count);
    //@ ensures characters(text, count) &*& characters(key, count);
{
    if (count > 0) {
        //@ open characters(text, count);
        //@ open characters(key, count);
        *text = (char)(*text ^ *key);
        xorchars(text + 1, key + 1, count - 1);
        //@ close characters(text, count);
        //@ close characters(key, count);
    }
}

void putchars(char *start, int count)
    //@ requires characters(start, count);
    //@ ensures characters(start, count);
{
    if (count > 0) {
        //@ open characters(start, count);
        char c = *start;
        putchar(c);
        putchars(start + 1, count - 1);
        //@ close characters(start, count);
    }
}

int main()
    //@ requires true;
    //@ ensures true;
{
    char *text = malloc(10);
    char *key = malloc(10);
    getchars(text, 10);
    getchars(key, 10);
    xorchars(text, key, 10);
    putchars(text, 10);
    //@ leak characters(text, 10) &*& characters(key, 10);
    return 0;
}
