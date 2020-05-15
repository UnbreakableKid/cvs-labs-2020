
/*@
predicate QueueInv(Queue q; int n, int m) =
	q.n |-> n
	&*& q.front |-> ?f
	&*& q.end |-> ?e
	&*& q.maxElements |-> m
	&*& q.elements |-> ?a
	&*& a.length == m
	&*& 0 <= n &*& n <= m
	&*& 0 <= f &*& f < m
        &*& 0 <= e &*& e < m
	&*& array_slice(a,0,m,?items);
@*/


//Queue based on a circular buffer.
class Queue {

  int n;
  int maxElements;
  Transaction[] elements;
  int front;
  int end;
  

  //creates a new Queue with capacity max.
  Queue(int max)
  //@ requires max > 0;
  //@ ensures QueueInv(this, 0, max);
  {
  
    front = 0;
    end = 0;
    n = 0;
    elements = new Transaction[max];
    maxElements = max;
  
  }

  //places the int v at the end of this Queue
  void enqueue(Transaction v)
  //@ requires QueueInv(this, ?x, ?m) &*& x < m;
  //@ ensures QueueInv(this, x+1, m);
  {
  

   elements[end] = v;
   
   end++;
   if (end == maxElements){
   	end = 0;
   
   }
   n++;


  
  }
  
  

  //retrieves the element at the start of this Queue.
  Transaction dequeue()
  //@ requires QueueInv(this, ?x, ?m) &*& x > 0 &*& this.elements |-> ?e &*& this.front |-> ?f;
  //@ ensures  QueueInv(this, x-1, m) &*& result == e[f] &*& TransInv(result, _,_,_);
  {
  
  
     Transaction result = elements[front];
     front++;
     if(front == maxElements ){
    	front = 0;
     }
     n--;
     return result;
  }
  
  //returns true if this Queue has reached its capacity.
  boolean isFull()
  //@requires QueueInv(this, ?x, ?m);
  //@ensures QueueInv(this, x, m) &*& result == (x == m);
  
  {
  
  return n == maxElements;
  
  }
  
  //returns true if this Queue has no elements.
  boolean isEmpty()
  //@requires QueueInv(this, ?x, ?m);
  //@ensures QueueInv(this, x, m) &*& result == (x==0);
  
  {

    return n == 0;

  }
  
  //public static void main(String[] args) {
	    
	//     // 101  111 = 010
	//     int hash = 90;
	// 	System.out.println(hash ^ ((hash & 3)));
	// 	System.out.println(hash & 1);
    //       System.out.println(hash & 2);



//	 }

}