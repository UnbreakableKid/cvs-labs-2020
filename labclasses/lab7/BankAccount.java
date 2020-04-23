/*
Starting point for exercise of Lab Session 6.
CVS course - Integrated Master in Computer Science and Engineering
@FCT UNL 2018
*/


/*@
predicate AccountInv(BankAccount o; int code, int bal, int limit) =
        o != null
    &*& o.balance |-> bal
    &*& o.accountid |-> code
    &*& o.climit |-> limit
    &*& limit >= 0
    &*& 0 <= bal + limit
    &*& 0 <= code &*& code <= 1000;
@*/

public class BankAccount {

  int balance;
  int climit;
  int accountid;

  public BankAccount(int id)
  //@ requires 0 <= id &*& id <= 1000;
  //@ ensures AccountInv(this, id, 0, 0);
  {
      balance = 0;
      climit = 0;
      accountid = id;
  }

  public void deposit(int v)
  //@ requires AccountInv(this,?c,?b, _) &*& v >= 0;
  //@ ensures AccountInv(this,c,b+v, _);
  {
  	balance += v;
  }

  public void withdraw(int v)
  //@ requires AccountInv(this,?c,?b, ?l) &*& 0 <= v &*& v <= b+l;
  //@ ensures AccountInv(this,c,b-v, l);
  {
     balance  -= v;
  }

  public int getcode()
  //@ requires AccountInv(this,?c,?b,?l);
  //@ ensures AccountInv(this,c,b,l) &*& result == c;  
  {
     return accountid;
  }

	
  public int getbalance()
  //@ requires AccountInv(this,?c,?b,?l);
  //@ ensures AccountInv(this,c,b,l) &*& result == b;  
  {
     return balance;
  }

  public void setclimit(int cl)
  //@ requires AccountInv(this,?c,?b,_) &*& cl >= 0 &*& -cl <= b;
  //@ ensures AccountInv(this,c,b,cl);
  {
      climit = cl;
  }

  public int getclimit()
  //@ requires this.climit |-> ?l;
  //@ ensures this.climit |-> l &*& result == l;
  {
     return climit;
  }

  static void main()
  {
    BankAccount b1 = new BankAccount(1000);
    b1.setclimit(500);
  }
}
