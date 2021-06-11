int main()
//@ requires true;
//@ ensures true;
{
    int *i = new int;
    //@ leak new_block_ints(i, 1);
    //@ leak integer(i, _);
    unsigned int *ui = new unsigned int;
    //@ leak new_block_uints(ui, 1);
    //@ leak u_integer(ui, _);
    signed int *si = new signed int;
    //@ leak new_block_ints(si, 1);
    //@ leak integer(si, _);
    short int *shi = new short int;
    //@ leak new_block_shorts(shi, 1);
    //@ leak short_integer(shi, _);
    unsigned short *us = new unsigned short;
    //@ leak new_block_ushorts(us, 1);
    //@ leak u_short_integer(us, _);
    long long *ll = new long long;
    //@ leak new_block_llongs(ll, 1);
    //@ leak llong_integer(ll, _);
    unsigned long long *ull = new unsigned long long;
    //@ leak new_block_ullongs(ull, 1);
    //@ leak u_llong_integer(ull, _);
    bool *b = new bool;
    //@ leak new_block_bools(b, 1);
    //@ leak boolean(b, _);
    char *c = new char;
    //@ leak new_block_chars(c, 1);
    //@ leak character(c, _);
}