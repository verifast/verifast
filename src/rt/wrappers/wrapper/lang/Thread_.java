package wrapper.lang;

public class Thread_{
  InnerThread t;
  public Thread_(Runnable run){
    t=new InnerThread(run);
  }
  public void start(){
    t.start();
  }
  public void join(){
    try{
      t.join();
    }catch(InterruptedException e){
      throw new RuntimeException("Thread was interrupted.",e);
    }
    if(!t.done){
      if(t.e==null){
      throw new RuntimeException("Internal error occurred.");
      }else{
      throw new RuntimeException("Exception: ",t.e);
      }
    }
  }
}
class InnerThread extends Thread{
  Runnable run;
  Throwable e;
  boolean done;
  InnerThread(Runnable run){
    super();
    this.run=run;
  }
  public void run(){
    done=false;
    try{
      run.run();
      done=true;
    }catch(Throwable e1){
      e=e1;
    }
  }
}