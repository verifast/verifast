struct foo {
    int x;
    int y;
};

int main() //@ : main
    //@ requires true;
    //@ ensures true;
{
    struct foo f;
        
    (&f)->x = 4;
   
    int i = f.x;
    //@ assert i == 4;
    
    f.x = 5;
    int j = (&f)->x;
    //@ assert j == 5;
    
    int temp = f.x;
    //@ assert temp == 5;
    
    f.x = 7;
    f.y = 8;
    
    //@ assert f.x == 7 && f.y == 8;

    return 0;
}

