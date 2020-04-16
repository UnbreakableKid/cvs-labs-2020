public class Account {

  int checking;
  int savings;

  /*@ 
  predicate AccountInv(int c, int s) = 
  	this.checking |-> c 
	&*&
	this.savings |-> s
  	&*&
  	c >= 0
	&*&
	s >= 0
	&*&
	c <= c/2;
  @*/

  public Account()
  //@ requires true;
  //@ ensures AccountInv(0, 0);
  {
    savings = 0;
	checking = 0;
  }

}
