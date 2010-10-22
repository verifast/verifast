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

/*@

lemma void split_characters_chunk(char *start, int i)
    requires characters(start, ?count) &*& 0 <= i &*& i <= count;
    ensures characters(start, i) &*& characters(start + i, count - i);
{
    if (i == 0) {
        close characters(start, 0);
    } else {
        open characters(start, count);
        split_characters_chunk(start + 1, i - 1);
        close characters(start, i);
    }
}

lemma void merge_characters_chunk(char *start)
    requires characters(start, ?i) &*& characters(start + i, ?count) &*& 0 <= i &*& 0 <= count;
    ensures characters(start, i + count);
{
    open characters(start, i);
    if (i != 0) {
        merge_characters_chunk(start + 1);
        close characters(start, i + count);
    }
}

@*/

void getchars(char *start, int count)
    //@ requires characters(start, count);
    //@ ensures characters(start, count);
{
    for (int i = 0; i < count; i++)
        //@ invariant characters(start, count) &*& 0 <= i;
    {
        char c = getchar();
        //@ split_characters_chunk(start, i);
        //@ open characters(start + i, count - i);
        *(start + i) = c;
        //@ close characters(start + i, count - i);
        //@ merge_characters_chunk(start);
    }
}

void putchars(char *start, int count)
    //@ requires characters(start, count);
    //@ ensures characters(start, count);
{
    for (int i = 0; i < count; i++)
        //@ invariant characters(start, count) &*& 0 <= i;
    {
        //@ split_characters_chunk(start, i);
        //@ open characters(start + i, count - i);
        char c = *(start + i);
        //@ close characters(start + i, count - i);
        //@ merge_characters_chunk(start);
        putchar(c);
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
