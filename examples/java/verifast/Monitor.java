package verifast;

public final class Monitor {
    
    boolean hasPayload = false;
    
    public Monitor()
    {
        hasPayload = true;
    }
    
    public void sync(CriticalSection body)
    {
        synchronized (this) {
            if (!hasPayload)
                throw new MonitorException();
            hasPayload = false;
            body.run();
            hasPayload = true;
        }
    }
    
}