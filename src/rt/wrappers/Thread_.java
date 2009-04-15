public class Thread_{
  Thread t;
  Exception e;
  public Thread_(Runnable run){
    t=new Thread(run);
  }
  void start(){
    try{
      t.run();
    }catch(RuntimeException e1){
      e=e1;
    }
  }
  void join(){
    try{
      t.join();
    }catch(InterruptedException e){
      throw new RuntimeException("Thread was interrupted.");
    }
    if(e!=null)
      throw new RuntimeException("An exception occurred");
  }
}