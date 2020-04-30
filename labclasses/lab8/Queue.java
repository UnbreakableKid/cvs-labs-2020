
class Queue {

  //creates a new Queue with capacity max.
  Queue(int max);

  //places the int v at the end of this Queue
  void enqueue(int v);

  //retrieves the element at the start of this Queue.
  int dequeue();
  
  //returns true if this Queue has reached its capacity.
  boolean isFull();
  
  //returns true if this Queue has no elements.
  boolean isEmpty();

}