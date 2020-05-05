/*
VERIFAST example of verified Java program 
CVS course - Integrated Master in Computer Science and Engineering
@FCT UNL João Costa Seco 2018
*/

/*@
  predicate Positive(unit a, int v; unit n) = v >= 0 &*& n == unit;
@*/


public class Bag {

  int store[];
  int nelems;


/*@

  predicate BagInv(int n, list<int> elems, list<int> others) =
      store |-> ?s 
  &*& nelems |-> n 
  &*& s != null 
  &*& 0<=n &*& n <= s.length 
  &*& array_slice_deep(s,0,n,Positive,unit,elems,_)
  &*& array_slice(s,n,s.length,others)
  ;
@*/

public Bag(int size)
  //@ requires size >= 0;
  //@ ensures BagInv(0,_,_);
{
  store = new int[size];
  nelems = 0;
}

boolean add(int v)
  //@ requires BagInv(?m,_,_) &*& v >= 0;
  //@ ensures result ? BagInv(m+1,_,_) : BagInv(m,_,_);
{
   //@ open BagInv(?n,?elems,?others);
  if(nelems<store.length) {
   //@ array_slice_split(store,n,n+1);
   store[nelems] = v;
   //@ array_slice_deep_close(store,nelems,Positive,unit);
   //@ array_slice_deep_join(store,0);
   nelems = nelems+1;
   //@ close BagInv(n+1,_,_);
   return true;
  } else { 
   //@ close BagInv(n,_,_);
   return false;
  }
}

int get(int i)
  //@ requires BagInv(?n,_,_) &*& 0 <= i &*& i < n;
  //@ ensures BagInv(n,_,_);
{
  return store[i];
}


int size() 
  //@ requires BagInv(?n,_,_);
  //@ ensures BagInv(n,_,_) &*& result>=0 ; 
{
  return nelems;
}


}

