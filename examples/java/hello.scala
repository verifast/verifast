object Program {
    def main(args: Array[String]): Unit
        //@ requires true
        //@ ensures true
    = {
        var x: Int = 5;
        var y: Int = 6;
        var z: Int = x + y;
        assert(z == 11);
    }
}