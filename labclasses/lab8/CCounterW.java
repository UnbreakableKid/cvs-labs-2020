import java.util.concurrent.locks.*;

/*@

predicate_ctor CCounter_shared_state (CCounter c) () =
   c.N |-> ?v &*& v >= 0 &*& c.MAX |-> ?m &*& m > 0 &*& v <= m;

predicate_ctor CCounter_nonzero (CCounter c) () =
   c.N |-> ?v &*& c.MAX |-> ?m &*& v > 0 &*& m > 0 &*& v <= m; 

predicate_ctor CCounter_nonmax (CCounter c) () =
   c.N |-> ?v &*& c.MAX |-> ?m &*& v < m &*& m > 0 &*& v >= 0; 
   
predicate inv(CCounter c) =  
         c.mon |-> ?l 
     &*& l!=null 
     &*& lck(l,1,CCounter_shared_state(c))
     &*& c.notzero |-> ?cc 
     &*& cc !=null 
     &*& cond(cc,CCounter_shared_state(c),CCounter_nonzero(c))
     &*& c.notmax |-> ?cm 
     &*& cm !=null 
     &*& cond(cm,CCounter_shared_state(c),CCounter_nonmax(c));
 
@*/

public class CCounter {

  int N;
  int MAX;
  ReentrantLock mon;
  Condition notzero; 
  Condition notmax; 

public CCounter(int max)
//@ requires max > 0;
//@ ensures inv(this);
{
 MAX = max;
  //@ close CCounter_shared_state(this)();
  //@ close enter_lck(1,CCounter_shared_state(this));
  mon = new ReentrantLock();
  //@ close set_cond(CCounter_shared_state(this),CCounter_nonzero(this));  
  notzero = mon.newCondition();
  //@ close set_cond(CCounter_shared_state(this),CCounter_nonmax(this));  
  notmax = mon.newCondition();
  //@ close inv(this);
}

public void inc() 
  //@ requires inv(this);
  //@ ensures inv(this);
  {
  //@ open inv(this);
   mon.lock();
   //@ open CCounter_shared_state(this)();
   while (N == MAX) 
   /*@ invariant this.N |-> ?v 
             &*& v >= 0 
             &*& this.MAX |-> ?m 
             &*& m > 0 &*& v <= m 
             &*& this.notmax |-> ?cm 
             &*& cm !=null 
             &*& cond(cm,CCounter_shared_state(this),CCounter_nonmax(this));
   @*/
   {
    //@ close CCounter_shared_state(this)();
    try { notmax.await(); } catch(InterruptedException e) {}
    //@ open CCounter_nonmax(this)(); 
   }
   N++;
   //@ close CCounter_nonzero(this)(); 
   notzero.signal();
   mon.unlock();
  //@ close inv(this);
}

public void dec()
//@ requires inv(this);
//@ ensures inv(this);
{
    //@ open inv(this);
    mon.lock();
    //@ open CCounter_shared_state(this)();
    while (N==0) 
    /*@ invariant this.N |-> ?v 
             &*& v >= 0 
             &*& this.MAX |-> ?m 
             &*& m > 0 &*& v <= m 
             &*& this.notzero |-> ?cc 
             &*& cc !=null 
             &*& cond(cc,CCounter_shared_state(this),CCounter_nonzero(this));
    @*/      
    {
      //@ close CCounter_shared_state(this)();
      notzero.await();
      //@ open CCounter_nonzero(this)();
      //@ assert N>=0;
    }
    N--;
    //@ close CCounter_nonmax(this)(); 
    notmax.signal();
    mon.unlock();
    //@ close inv(this);
  } 
}
