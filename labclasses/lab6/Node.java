
/*@
  predicate Node(Node t; Node n, int v) =
        t.nxt |-> n 
    &*& t.val |-> v;

  predicate List(Node n;) =
    n == null ? true : Node(n, ?nn, _) &*& List(nn);
@*/

class Node {

  private Node nxt;
  private int val;
  
  public Node()
  //@ requires true;
  //@ ensures Node(this, null, 0);
  {
    nxt = null;
    val = 0;
  }
  
  public Node(int v)
  //@ requires true;
  //@ ensures Node(this, null, v);
  {
    nxt = null;
    val = v;
  }
  
  public Node(int v, Node n)
  //@ requires true;
  //@ ensures Node(this, n, v);
  {
    nxt = n;
    val = v;
  }
  
  public Node getNext()
  //@ requires Node(this, ?n, ?v);
  //@ ensures Node(this, n, v) &*& result == n;
  {
    return nxt;
  }
  
  public int getValue()
  //@ requires Node(this, ?n, ?v);
  //@ ensures Node(this, n, v) &*& result == v;
  {
    return val;
  }
  
  public void setNext(Node n)
  //@ requires Node(this, _, ?v);
  //@ ensures Node(this, n, v);
  {
    nxt = n;
  }
  
  public void setValue(int v)
  //@ requires Node(this, ?n, _);
  //@ ensures Node(this, n, v);
  {
    val = v;
  }
  
}