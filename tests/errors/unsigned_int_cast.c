int main() //@ : main
//@ requires true;
//@ ensures true;
{
    int z = -1;
    unsigned int z2 = (unsigned int) z; //~ should-fail
    /*
    z2 = z2 + 1;
    if ((unsigned int)z > z2){
        int *evil = 0;
        *evil = 0;
        // If the cast to unsigned int would just pass,
        // VeriFast would think the above code
        // never gets executed.
    }
    return 0;
    */
}
