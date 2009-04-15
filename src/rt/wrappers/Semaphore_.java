import java.util.concurrent.*;
public class Semaphore_ extends Object{
  Semaphore obj;
  Semaphore_(int n){
  obj=new Semaphore(n);
  }
  void acquire(){
  try{
    obj.acquire();
  }catch(InterruptedException e){
    throw new RuntimeException("Thread was interrupted"); 
  }
  }
  void release(){
    obj.release();
  }
}