class Program {

    public static boolean getRandomBool()
        //@ requires true;
        //@ ensures true;
    {
        return Math.random() < 0.5;
    }

}
