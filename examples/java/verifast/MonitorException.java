package verifast;

public class MonitorException extends RuntimeException {
    
    public MonitorException() {
        super("Monitor re-entered without intervening normal exit: re-entry in same thread or after exceptional exit");
    }
    
}
