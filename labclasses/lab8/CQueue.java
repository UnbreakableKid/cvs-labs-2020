import java.util.concurrent.*;
import java.util.concurrent.locks.*;


/*@

predicate_ctor CQueue_shared_state (CQueue c)() = 
    c.queue |-> ?q 
    &*& q != null 

    &*& QueueInv(q, _, _);


predicate CQueueInv(CQueue c;) =
	c.mon |-> ?m
	&*& m != null
        &*& lck(m, 1, CQueue_shared_state(c))

	;
@*/


public class CQueue {

  Queue queue;
  ReentrantLock mon;
 
  CQueue(int max)
  //@requires max > 0;
  //@ensures CQueueInv(this);
  {
  
   queue = new Queue(max);
   
  
   
   //@close CQueue_shared_state(this)();
   //@ close enter_lck(1, CQueue_shared_state(this));
   mon = new ReentrantLock();

    //@ close CQueueInv(this);

  }

  void enqueue(int v)
  //@ requires CQueueInv(this);
  //@ ensures CQueueInv(this);
  {
 
    //@open CQueueInv(this);
    mon.lock();
    
    //@open CQueue_shared_state(this)();
    
    queue.enqueue(v);
        
    //@close CQueue_shared_state(this)();

    mon.unlock();
    
        
    //@close CQueueInv(this);
  }

  int dequeue()
  
  
  {

   

  }

  boolean isFull()
  //@requires CQueueInv(this);
  //@ ensures CQueueInv(this);
  {
  
    //@open CQueueInv(this);
    mon.lock();
    //@open CQueue_shared_state(this)();
    
    
    boolean result = queue.isEmpty();
    
    //@close CQueue_shared_state(this)();
    mon.unlock();
    
    return result;
  }

  boolean isEmpty()
  //@requires CQueueInv(this);
  //@ensures CQueueInv(this);
  {
  
    //@open CQueueInv(this);
    mon.lock();
    //@open CQueue_shared_state(this)();
    
    
    boolean result = queue.isFull();
    
    //@close CQueue_shared_state(this)();
    mon.unlock();
    
    return result;
   
  }

}