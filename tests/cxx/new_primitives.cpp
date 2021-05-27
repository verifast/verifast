/*@
    // TODO: add to a c++ prelude
    predicate new_block(void *p; int size);
    predicate new_block_chars(char *p; int count) = new_block(p, count);
    predicate new_block_uchars(unsigned char *p; int count) = new_block(p, count);
    predicate new_block_ints(int *p; int count) = new_block(p, ?size) &*& [_]divrem(size, sizeof(int), count, 0);
    predicate new_block_uints(unsigned int *p; int count) = new_block(p, ?size) &*& [_]divrem(size, sizeof(unsigned int), count, 0);
    predicate new_block_shorts(short *p; int count) = new_block(p, ?size) &*& [_]divrem(size, sizeof(short), count, 0);
    predicate new_block_ushorts(unsigned short *p; int count) = new_block(p, ?size) &*& [_]divrem(size, sizeof(unsigned short), count, 0);
    predicate new_block_pointers(void **p; int count) = new_block(p, ?size) &*& [_]divrem(size, sizeof(void *), count, 0);
    predicate new_block_llongs(long long *p; int count) = new_block(p, ?size) &*& [_]divrem(size, sizeof(long long), count, 0);
    predicate new_block_ullongs(unsigned long long *p; int count) = new_block(p, ?size) &*& [_]divrem(size, sizeof(unsigned long long), count, 0);
    predicate new_block_bools(bool *p; int count) =  new_block(p, ?size) &*& [_]divrem(size, sizeof(bool), count, 0);
    predicate new_block_floats(float *p; int count) = new_block(p, ?size) &*& [_]divrem(size, sizeof(float), count, 0);
    predicate new_block_doubles(double *p; int count) = new_block(p, ?size) &*& [_]divrem(size, sizeof(double), count, 0);
    predicate new_block_long_doubles(long double *p; int count) = new_block(p, ?size) &*& [_]divrem(size, sizeof(long double), count, 0);
@*/

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