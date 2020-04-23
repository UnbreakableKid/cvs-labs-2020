  /*@ 
  predicate AccountInv(Account a; int b) = 
    a != null
    &*& a.balance |-> b
    &*& b >= 0;
  @*/
  
  public class Account {

  int balance;



  public Account()
  //@ requires true;
  //@ ensures AccountInv(this, 0);
  {
	balance = 0;
	//@ close AccountInv(this, 0);
  }
  
  public void deposit(int n)
  //@ requires AccountInv(this, ?b) &*& n > 0;
  //@ ensures AccountInv(this, b + n);
  
  {	
  	//@ open AccountInv(this, b);
  	balance += n;
  	//@ close AccountInv(this, b+n);
  	
  }
  
  public void withdraw(int n)
  //@ requires AccountInv(this, ?b) &*& n > 0;
  //@ensures n <= b ? AccountInv(this, b - n) : AccountInv(this, b);
  {
  	if(n <= balance) {
	  	balance -= n;
  	}
  } 

}
