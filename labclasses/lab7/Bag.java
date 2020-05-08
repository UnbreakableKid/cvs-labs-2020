/*
Starting point for exercise of Lab Session 6.
CVS course - Integrated Master in Computer Science and Engineering
@FCT UNL Eduardo Geraldo, João Costa Seco 2019
*/

/*@  predicate Positive(unit a, int v; unit n) = v >= 0 &*& n == unit; 
     predicate noteq(int elem, int v; unit n) = elem != v &*& n ==unit;
     
     
   predicate NotEq(PositiveBag bag, int idx, int elem; int[]s, int n, int c) = 
    bag.array |-> s
    &*& bag.nelems |->n
    &*& bag.capacity |-> c
    &*& s!= null &*& s.length == c
    &*& 0<= idx &*& idx <= n
    &*& array_slice_deep(s, 0, idx, noteq, elem, _,_)
    &*& array_slice(s, idx, n, _)
    &*& array_slice(s,n,c ,?others);
    
    
    predicate Equal(PositiveBag bag, int idx, int elem; int[]s, int n, int c) =
    
     bag.array |-> s
     &*& bag.nelems |->n
     &*& bag.capacity |-> c
     &*& s!= null &*& s.length == c
     &*& 0<=idx &*& idx <= n
     &*& array_slice_deep(s, 0, idx, noteq, elem, _,_)
     &*& array_slice(s, idx, idx+1, ?vals)
     &*& head(vals) == elem
     &*& array_slice(s, idx+1, n, _)
     &*& array_slice(s,n,c ,_);
@*/


 
class PositiveBag {

    int[] array;
    int nelems;
    int capacity;

    /*
     * Initializaes the underlying qarray with the length size.
     */
  /*@
    predicate BagInv(int n, int c) =
    array |-> ?s
    &*& nelems |-> n
    &*& capacity |-> c 
    &*& s.length == c
    &*& s != null
    &*& 0 <= n &*& n <= c
    &*& array_slice_deep(s, 0 , n, Positive, unit, ?elems, _)
    &*& array_slice(s,n,s.length,?others)
    ;
    
    
    
    @*/
    
    public PositiveBag(int size) 
	//@ requires size > 0;
	//@ ensures BagInv(0,size);
    {
	array = new int[size];
	nelems = 0;
	capacity = size;
    }
	
    public int get(int i)
    //@ requires BagInv(?n,?c) &*& 0 <= i &*& i < n;
    //@ ensures true;
    {
    	return array[i];
    }
	
	
    /*
     * Inserts the integer v into this bag.
     */
     
/*
 
    public void insert(int v) 

	//@ requires BagInv(?n, ?c) &*& n < c ;
	//@ ensures BagInv(n+1, c);
	{
	
	
	 array[nelems] = v;
	 nelems = nelems+1;
	 //@ array_slice_deep_close(array,n, Positive, unit);
	}
	
	*/

    /*
     * Returns the index of the first occurrence of f in this bag. If the value
     * v is not in this bag, this operation returns -1.
     */
    public int indexOf(int elem)
        //@ requires BagInv(this, ?array, ?n, ?c);
        //@ ensures result == -1 ? NotEq(this, n, elem, array, n, c) : Equal(this, result, elem, _,_,_);
        {
         int i = 0;
         
         //@ open BagInv(_,_);
         //@ array_slice_deep_open(array,0);
         //@ close NotEq(this, i, elem, _, _);
    	 
    	 while(i < nelems)
    	 //@invariant array_slice_deep(array, 0, i, noteq, elem, _,_);
      	 {
    	   if (array[i] == elem){    	 
               return i;
	   }
	   i++;
    	 }
    	 
    	 return -1;
    	
        }
    
    
    /*
     * Removes the element at index idx from this bag.
     */
    public void remove(int idx) {}

}
