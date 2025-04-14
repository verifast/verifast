class ConstOverflow {
  public static final int FOO1 = -0x80000000;
  public static final int FOO2 = 0x40000000 + 0x40000000;
  public static final int FOO3 = -0x40000000 - 0x40000000;
  public static final int FOO4 = -0x60000000 - 0x60000000;
  public static final int FOO5 = 0x10000 * 0x10000;

  public static final long BAR1 = -0x80000000_00000000L;
  public static final long BAR2 = 0x40000000_00000000L + 0x40000000_00000000L;
  public static final long BAR3 = -0x40000000_00000000L - 0x40000000_00000000L;
  public static final long BAR4 = -0x60000000_00000000L - 0x60000000_00000000L;
  public static final long BAR5 = 0x100000000L * 0x100000000L;

  public static void test()
  //@ requires true;
  //@ ensures true;
  {
    //@ assert Integer.MIN_VALUE < 0;
    //@ assert Integer.MIN_VALUE == -0x80000000;
    
    //@ assert FOO1 < 0;
    //@ assert FOO1 == -0x80000000;
    //@ assert FOO2 < 0;
    //@ assert FOO2 == -0x80000000;
    //@ assert FOO3 < 0;
    //@ assert FOO3 == -0x80000000;
    //@ assert FOO4 == 0x40000000;
    //@ assert FOO5 == 0;

    //@ assert BAR1 < 0;
    //@ assert BAR1 == -0x80000000_00000000;
    //@ assert BAR2 < 0;
    //@ assert BAR2 == -0x80000000_00000000;
    //@ assert BAR3 < 0;
    //@ assert BAR3 == -0x80000000_00000000;
    //@ assert BAR4 == 0x40000000_00000000;
    //@ assert BAR5 == 0;
  }
}
