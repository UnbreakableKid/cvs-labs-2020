
/* Class representing a bounded counter. The value of this counter is restricted 
 by a set limit upon its creation. Once the value of the counter reaches the
 limit, its is no longer possible to call the inc(); The operation inc()
 increases the value of the counter by 1. To reduce the value, the counter
 has the operation dec(). This operation decreases the value of the counter by 1
 until the value reaches 0.
*/
class BCounter {

  BCounter(int max){}

  void inc(){}

  void dec(){}
  
  int get(){}

  int getMax(){}
  
  public static void main(String[] args) {}
}