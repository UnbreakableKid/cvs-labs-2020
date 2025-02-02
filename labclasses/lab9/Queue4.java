import java.util.concurrent.locks.*;

/*@

  predicate AInv(A a;) = a.a |-> ?v &*& v >= 0;

  predicate P(unit a, A v; unit b) = v != null &*& AInv(v) &*& b == unit;

  predicate QueueInv(Queue q, predicate(unit, A;unit) p; int n, int m) = 

        q.array |-> ?a
    &*& q.numelements |-> n
    &*& q.head |-> ?h
    &*& q.tail |-> ?t

    &*& a != null
    &*& (h < t || n == a.length ? 
                ( array_slice_deep(a, 0, h, p, unit,  ?in1, _) 
              &*& array_slice(a, h, t, ?out) 
              &*& array_slice_deep(a, t, a.length, p, unit, ?in2, _)) 
            :
            (
             ( array_slice(a, 0, t, ?out1) 
            &*& array_slice_deep(a, t, h, p, unit, ?in,_) 
            &*& array_slice(a, h, a.length, ?out2)) 
            )
         )
    &*& m == a.length
    &*& 0 <= n &*& n <= a.length
    &*& 0 <= h &*& h < a.length
    &*& 0 <= t &*& t < a.length

    &*& (h == t ? n == 0 || n == a.length : true)
    &*& (h > t  ? n == h - t : true)
    &*& (h < t  ? n == h - t + a.length : true)
    ;
@*/

class A {
	int a;
	
	public A(int A) {
		this.a = a;
	}
}

class Queue {

  A[] array;
  int numelements;
  int head;
  int tail;

  Queue(int size)
  //@ requires size > 0;
  //@ ensures QueueInv(this, P, 0, size);
  {
    array = new A[size];
    numelements = 0;
    head = 0;
    tail = 0;
  }

  void enqueue(A v) 
  //@ requires QueueInv(this, P, ?n, ?m) &*& n < m &*& v != null &*& AInv(v);
  //@ ensures QueueInv(this, P, n+1, m);
  {
    //@ array_slice_split(array, head, head+1);
    array[head++] = v;
    //@ array_slice_deep_close(array, head-1, P, unit);
    if( head == array.length ) head = 0;
    numelements++;
  }

  A dequeue() 
  //@ requires QueueInv(this, P, ?n, ?m) &*& n > 0;
  //@ ensures QueueInv(this, P, n-1, m);
  {
    A v = array[tail++];
    if( tail == array.length ) tail = 0;
    numelements--;
    return v;
  }

  boolean isFull() 
  //@ requires QueueInv(this, P, ?n, ?m);
  //@ ensures QueueInv(this, P, n, m) &*& result == (n == m);
  {
    return numelements == array.length;
  }

  boolean isEmpty() 
  //@ requires QueueInv(this, P, ?n, ?m);
  //@ ensures QueueInv(this, P, n, m) &*& result == (n == 0);
  {
    return numelements == 0;
  }
}

/*@

predicate_ctor CQueue_shared_state(CQueue cq)() = cq.q |-> ?q &*& q != null &*& QueueInv(q,P,_,_);

predicate_ctor CQueue_nonempty(CQueue cq)() = cq.q |-> ?q &*& q != null &*& QueueInv(q,P,?n,_) &*& n > 0;

predicate_ctor CQueue_nonfull(CQueue cq)() = cq.q |-> ?q &*& q != null &*& QueueInv(q,P,?n,?m) &*& n < m;

predicate CQueueInv(CQueue cq;) =
        cq.mon |-> ?l
    &*& cq.notempty |-> ?ce
    &*& cq.notfull |-> ?cf

    &*& l != null
    &*& ce != null
    &*& cf != null

    &*& lck(l, 1, CQueue_shared_state(cq))
    &*& cond(ce, CQueue_shared_state(cq), CQueue_nonempty(cq))
    &*& cond(cf, CQueue_shared_state(cq), CQueue_nonfull(cq));

@*/

class CQueue {

  Queue q;

  ReentrantLock mon;
  Condition notempty;
  Condition notfull;

  CQueue(int size)
  //@ requires size > 0;
  //@ ensures CQueueInv(this);
  {
    q = new Queue(size);
    //@ close CQueue_shared_state(this)();
    //@ close enter_lck(1, CQueue_shared_state(this));
    mon = new ReentrantLock();
    //@ close set_cond(CQueue_shared_state(this), CQueue_nonempty(this));
    notempty = mon.newCondition();
    //@ close set_cond(CQueue_shared_state(this), CQueue_nonfull(this));
    notfull = mon.newCondition();
  }

  void enqueue(A v)  
  //@ requires CQueueInv(this) &*& v != null &*& AInv(v);
  //@ ensures CQueueInv(this);
  {
    mon.lock();
    //@ open CQueue_shared_state(this)();
    if( q.isFull() ) {
      //@ close CQueue_shared_state(this)();
      notfull.await();
      //@ open CQueue_nonfull(this)();
    }
    //@ open QueueInv(q,_,_,_);
    q.enqueue(v);
    //@ close CQueue_nonempty(this)();
    notempty.signal();
    mon.unlock();
  }

  A dequeue() 
  //@ requires CQueueInv(this);
  //@ ensures CQueueInv(this);
  {
    mon.lock();
    //@ open CQueue_shared_state(this)();
    if( q.isEmpty() ) {
      //@ close CQueue_shared_state(this)();
      notempty.await();
      //@ open CQueue_nonempty(this)();
    }
    //@ open QueueInv(q,_,_,_);
    A v = q.dequeue();
    //@ close CQueue_nonfull(this)();
    notfull.signal();
    mon.unlock();
    return v;
  }
}