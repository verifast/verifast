void modify_ints_refs_old_syntax(int* first, int* second)
    //@ requires integer(first, ?val1) &*& integer(second, ?val2);
    //@ ensures integer(first, val1 + 1) &*& integer(second, val2 - 1);
{
    (*first)++;
    (*second)--;
}

void modify_ints_refs_new_syntax(int* first, int* second)
    //@ requires *first |-> ?val1 &*& *second |-> ?val2;
    //@ ensures *first |-> val1 + 1 &*& *second |-> val2 - 1;
{
    (*first)++;
    (*second)--;
}

void modify_uints_refs_old_syntax(unsigned int* first, unsigned int* second)
    //@ requires u_integer(first, ?val1) &*& u_integer(second, ?val2);
    //@ ensures u_integer(first, val1 + 1) &*& u_integer(second, val2 - 1);
{
    *first = *first + 1;
    *second = *second - 1;
}

void modify_uints_refs_new_syntax(unsigned int* first, unsigned int* second)
    //@ requires *first |-> ?val1 &*& *second |-> ?val2;
    //@ ensures *first |-> val1 + 1 &*& *second |-> val2 - 1;
{
    *first = *first + 1;
    *second = *second - 1;
}

void modify_chars_refs_old_syntax(char* first, char* second)
    //@ requires character(first, ?val1) &*& character(second, ?val2);
    //@ ensures character(first, (char) (val1 + 1)) &*& character(second, (char) (val2 - 1));
{
    (*first)++;
    (*second)--;
}

void modify_chars_refs_new_syntax(char* first, char* second)
    //@ requires *first |-> ?val1 &*& *second |-> ?val2;
    //@ ensures *first |-> (char) (val1 + 1) &*& *second |-> (char) (val2 - 1);
{
    (*first)++;
    (*second)--;
}

int main() //@ : main
    //@ requires true;
    //@ ensures true;
{
    int i = -10;
    int j = 10;
    unsigned int k = 10;
    unsigned int l = 20;
    char m = 'a';
    char n = 'z';
    
    //@ assert i == -10 && j == 10;
    modify_ints_refs_old_syntax(&i, &j);
    //@ assert i == -9 && j == 9;
    modify_ints_refs_new_syntax(&i, &j);
    //@ assert i == -8 && j == 8;

    
    //@ assert k == 10 && l == 20;
    modify_uints_refs_old_syntax(&k, &l);
    //@ assert k == 11 && l == 19;
    modify_uints_refs_new_syntax(&k, &l);
    //@ assert k == 12 && l == 18;    
    
    
    //@ assert m == 'a' && n == 'z';
    modify_chars_refs_old_syntax(&m, &n);
    //@ assert m == 'b' && n == 'y';
    modify_chars_refs_new_syntax(&m, &n);
    //@ assert m == 'c' && n == 'x';
    
    return 0;
}


