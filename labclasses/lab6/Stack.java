
/*@
  predicate StackInv(Stack t;) = 
        t.head |-> ?h
    &*& List(h);
    
  predicate NonEmptyStack(Stack t;) = 
    t.head |-> ?h
    &*& h != null
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
  
  public int pop_maybe()
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
  
  public int pop()
    //@ requires NonEmptyStack(this);
  //@ ensures StackInv(this);
  {
  
      int val = head.getValue();
      head = head.getNext();
      return val;
  }
  
  public boolean isEmpty()
  //@ requires StackInv(this);
  //@ ensures result?StackInv(this):NonEmptyStack(this);
  {
  	
  	return head == null;
  
  }
  
}