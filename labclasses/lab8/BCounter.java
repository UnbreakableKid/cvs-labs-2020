
/* Class representing a bounded counter. The value of this counter is restricted 
 by a set limit upon its creation. Once the value of the counter reaches the
 limit, its is no longer possible to call the inc(); The operation inc()
 increases the value of the counter by 1. To reduce the value, the counter
 has the operation dec(). This operation decreases the value of the counter by 1
 until the value reaches 0.
*/



/*@
	predicate BCounterInv(BCounter c; int v, int m) = c.n |-> v &*& 
		c.max |-> m &*& v>=0 &*& v <= m;

@*/

class BCounter {

  int n;
  int max;



  BCounter(int m)
  //@ requires m >= 0;
  //@ ensures BCounterInv(this, 0, m);
  {
  
	  n = 0;
	  max = m;

  
  }

  void inc()
  //@ requires BCounterInv(this, ?x, ?m) &*& x < m;
  //@ ensures BCounterInv(this, x+1, m);
  
  {

  	n++;


  }

  void dec()
  //@ requires BCounterInv(this, ?x, ?m) &*& x >0;
  //@ ensures BCounterInv(this, x-1, m);
  {
  

  	n--;

  }
  
  int get()
  //@ requires BCounterInv(this, ?x, ?m);
  //@ ensures BCounterInv(this, x, m) &*& 0<=result &*& result <= m;
  {
  
  	return n;
  }

  int getMax(){
  
  	return max;
  }
  
  public static void main(String[] args) 
  //@ requires true;
  //@ ensures true;
  {	
  	int MAX = 100;
	BCounter c = new BCounter(MAX);
	//@ assert BCounterInv(c,0,MAX);

	if (c.get() < MAX) {
		//@ assert BCounterInv(c,?v,MAX) &*& v<MAX;
		c.inc(); 
	}
	  
  }
}