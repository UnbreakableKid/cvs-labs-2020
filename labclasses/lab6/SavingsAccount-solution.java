/*@predicate AccInv(SavingsAccount a; int s, int c) =
       a != null
   &*& a.sav |-> s
   &*& s >=0
   &*& a.chk |-> c
   &*& c >= -(s/2);
@*/



public class SavingsAccount {

  int sav;
  int chk;


  public SavingsAccount()
  //@ requires true; 
  //@ ensures AccInv(this, 0, 0);
  {
    sav = 0;
    chk = 0;
  }


  void deposit(int v)
  //@ requires AccInv(this, ?s, ?c) &*& v >= 0;
  //@ ensures AccInv (this, s, c + v);
  {
    chk += v;
  }

  void withdraw(int v)
  //@ requires AccInv(this, ?s, ?c) &*& 0 <= v;
  //@ ensures v <= c + s/2 ? AccInv(this, s, c-v) : AccInv(this, s, c);
  {
    if(v <= chk + sav/2) {
      chk -= v;
    }
  }
  
  void save(int v)
  //@ requires AccInv(this, ?s, ?c) &*& v >= 0;
  //@ ensures c >= 0 ? AccInv(this, s + v, c) : AccInv(this, s, c);
  {
    if(chk >= 0) {
      sav += v;  
    }
  }
  
  void rescue(int v)
  //@ requires AccInv(this, ?s, ?c) &*& v >= 0;
  //@ ensures c >= 0 && v <= s || c <= 0 && v <= s + 2* c ? AccInv(this, s-v, c) : AccInv(this, s, c);
  {
    if((chk >= 0 && v <= sav) || (chk <= 0 && v <= sav + 2* chk)) {
      sav -= v;
    }
  }
  
  int getSavings()
  //@ requires AccInv(this, ?s, ?c);
  //@ ensures AccInv(this, s, c) &*& result == s; 
  {
    return sav;
  }
  
  int getChecking()
  //@ requires AccInv(this, ?s, ?c);
  //@ ensures AccInv(this, s, c) &*& result == c; 
  {
    return chk;
  }
  
  public static void transfer(SavingsAccount a1, SavingsAccount a2, int v)
  /*@
    requires
          a1 != null &*& AccInv(a1, ?s1, ?c1)
      &*& a2 != null &*& AccInv(a2, ?s2, ?c2)
      &*& v >= 0;
  @*/
  /*@
    ensures
      v <= c1+s1/2 
      ?
      AccInv(a1, s1, c1-v) &*& AccInv(a2, s2, c2+v)
      :
      AccInv(a1, s1, c1) &*& AccInv(a2, s2, c2);
  @*/
  {
    if(v <= a1.getChecking() + a1.getSavings()/2) {
      a1.withdraw(v);
      a2.deposit(v);
    }
  }
  
  public static void main(String[] args)
  //@ requires true;
  //@ ensures true;
  {
    SavingsAccount a1 = new SavingsAccount();
    SavingsAccount a2 = new SavingsAccount();
    
    a1.deposit(500);
    transfer(a1, a2, 250);
  }
  
}
