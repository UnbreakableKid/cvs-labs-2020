/*
Starting point for exercise of Lab Session 6.
CVS course - Integrated Master in Computer Science and Engineering
@FCT UNL Luis Caires 2015
*/

/*@
predicate AccountP(unit a,BankAccount c; int n) = c != null &*& AccountInv(c,n,?b,?l);
@*/

/*@
predicate BankInv(Bank bk; int n, int m) =
     bk.nelems |-> n &*&
     bk.capacity |-> m &*&
     m > 0 &*&
     bk.store |-> ?a &*&
     a != null &*&
     a.length == m &*&
     0 <= n &*& n<=m &*&
     array_slice_deep(a, 0, n, AccountP, unit,_,?bs) &*&
     array_slice(a, n, m,?rest) &*&
     all_eq(rest, null) == true ;
@*/


class Bank {

    BankAccount store[];
    int nelems;
    int capacity;

    public Bank(int size)
    //@ requires size > 0;
    //@ ensures BankInv(this, 0, size);
    {
        nelems = 0;
        capacity = size;
        store = new BankAccount[size];
    }

    void addnewAccount(int code)
    //@ requires BankInv(this, ?n, ?m) &*& 0 <= code &*& code <= 1000;
    //@ ensures n < m ? BankInv(this, n+1, m) : BankInv(this, n, m);
    {
        BankAccount c = new BankAccount(code);

        if (nelems < capacity) {
            store[nelems] = c;
            nelems = nelems + 1;
        }
    }

    int getbalance(int code)
    //@ requires BankInv(this, ?n, ?m);
    //@ ensures BankInv(this, n, m);
    {
        int i = 0;

        //@ open BankInv(this, n, m);

        while (i < nelems)
        //@ invariant BankInv(this,n,m) &*& 0 <= i &*& i <= n;
        {
            if (store[i].getcode() == code) {
                return store[i].getbalance();
            }
            i = i + 1;
        }
        throw new UnknownAccountException();
    }

    boolean removeAccount(int code)
    //@ requires BankInv(this, ?n, ?m);
    //@ ensures result ? BankInv(this, n-1, m) : BankInv(this, n, m);
    {
        int i = 0;

        //@ open BankInv(this, n, m);

        while (i < nelems)
        //@ invariant BankInv(this,n,m) &*& 0 <= i &*& i <= n;
        {
            if (store[i].getcode() == code) {

                BankAccount res = store[i];

                if (i < nelems - 1) {
                    store[i] == store[nelems - 1];
                }
                nelems = nelems - 1;
                store[nelems] = null;

                return true;
            }
            i = i + 1;
        }
        return false;
    }

    boolean transfer(int acc_code_from, int acc_code_to, int val)
    //@ requires BankInv(this,?n,?m) &*& val > 0;
    //@ ensures BankInv(this,n,m);
    {

        int i = 0;
        //@ open BankInv(this,n,m);
        while (i < nelems)
        //@ invariant BankInv(this,n,m) &*& 0 <= i &*& i <= n;
        {
            if (store[i].getcode() == acc_code_from) {
                int j = 0;
                // @ open BankInv(this,n,m);
                while (j < nelems)
                //@ invariant BankInv(this,n,m) &*& 0 <= j &*& j <= n &*& 0 <= i &*& i <= n;
                {
                    if (store[j].getcode() == acc_code_to) {
                        //@ close BankInv(this,n,m);
                        if (store[i].getbalance() + store[i].getclimit() >= val) {

                            store[i].withdraw(val);
                            //@ close BankInv(this,n,m);
                            store[j].deposit(val);
                        }
                        return true;
                    }
                    j = j + 1;
                }
            }
            i = i + 1;
        }

        return false;
    }

    void extendstore()
//@ requires BankInv(this,?n,?m);
//@ ensures BankInv(this,n,2*m);
    {
        int i = 0;
        BankAccount newstore[] = new BankAccount[capacity * 2];
        //@ open BankInv(this,n,m);
        while (i < nelems)
  /*@  invariant
       this.nelems |-> n &*& 
       this.capacity |-> m &*&
       this.store |-> ?a &*&
       a.length == m &*&
       0 <= n &*& n<=m &*& 
       array_slice(a, 0, i,?r1) &*& all_eq(r1, null) == true  &*&
       array_slice_deep(a, i, n, AccountP, unit,_,?bs) &*&
       array_slice(a, n, m,?rest) &*& all_eq(rest, null) == true &*&
       array_slice_deep(newstore, 0, i, AccountP, unit,_,_) &*&
       array_slice(newstore, i, m*2,?r2) &*& all_eq(r2, null) == true 
       &*& 0 <= i &*& i <= n;
     @*/ {
            newstore[i] = store[i];
            store[i] = null;
            i++;
        }
        capacity = 2 * capacity;
        store = newstore;
        return;
    }

}