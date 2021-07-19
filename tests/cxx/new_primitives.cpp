int main()
//@ requires true;
//@ ensures true;
{
    int *i = new int;
    delete i;
    unsigned int *ui = new unsigned int;
    delete ui;
    signed int *si = new signed int;
    delete si;
    short int *shi = new short int;
    delete shi;
    unsigned short *us = new unsigned short;
    delete us;
    long long *ll = new long long;
    delete ll;
    unsigned long long *ull = new unsigned long long;
    delete ull;
    bool *b = new bool;
    delete b;
    char *c = new char;
    delete c;
}