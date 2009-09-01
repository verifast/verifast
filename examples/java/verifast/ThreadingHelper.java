package verifast;

public class ThreadingHelper {
    public static JoinableRunnable createJoinableRunnable(Runnable r) {
        return new JoinableRunnable(r);
    }
    
    public static void join(Thread t, JoinableRunnable r) {
        try {
            t.join();
        } catch (InterruptedException e) {
            throw new RuntimeException(e);
        }
        if (!r.done) {
            throw new RuntimeException(r.exception);
        }
    }
}
