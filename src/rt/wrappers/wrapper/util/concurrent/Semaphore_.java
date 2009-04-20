package wrapper.util.concurrent;
import java.util.concurrent.*;
public class Semaphore_ extends Object{
  Semaphore obj;
  public Semaphore_(int n){
  obj=new Semaphore(n);
  }
  public void acquire(){
  try{
    obj.acquire();
  }catch(InterruptedException e){
    throw new RuntimeException("Thread was interrupted"); 
  }
  }
  public void release(){
    obj.release();
  }
}