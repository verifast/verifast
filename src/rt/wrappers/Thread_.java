public class Thread_{
  Thread t;
  public Thread_(Runnable run){
    t=new Thread(run);
  }
  void start(){
    t.start();
  }
  void join(){
    try{t.join();}
	catch(InterruptedException e){
	throw new RuntimeException("Thread was interrupted.");
	}
  }
}