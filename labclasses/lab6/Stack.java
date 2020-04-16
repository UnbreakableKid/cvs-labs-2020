
/*@
  predicate StackInv(Stack t;) = 
        t.head |-> ?h
    &*& List(h);
@*/

class Stack {

  private Node head;
  
  public Stack()
  //@ requires true;
  //@ ensures StackInv(this);
  {
    head = null;
  }
  
  public void push(int v)
  //@ requires StackInv(this);
  //@ ensures StackInv(this);
  {
    head = new Node(v, head);
  }
  
  public int pop()
  throws EmptyStackException //@ ensures StackInv(this);
  //@ requires StackInv(this);
  //@ ensures StackInv(this);
  {
    if (head != null) {
      int val = head.getValue();
      head = head.getNext();
      return val;
    }
    throw new EmptyStackException();
  }
  
}