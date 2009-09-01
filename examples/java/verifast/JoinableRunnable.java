package verifast;

public class JoinableRunnable implements Runnable {
    Runnable runnable;
    boolean done;
    Throwable exception;
    
    JoinableRunnable(Runnable runnable) {
        this.runnable = runnable;
    }
    
    public void run() {
        try {
            runnable.run();
            done = true;
        } catch (Error t) {
            exception = t;
            throw t;
        } catch (RuntimeException t) {
            exception = t;
            throw t;
        }
    }
}
