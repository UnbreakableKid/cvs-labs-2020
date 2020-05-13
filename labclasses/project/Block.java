/*
Construction and Verification of Software 2019/20.

Project assignment to implement and verify a simplified blockchain.

�2020 Jo�o Costa Seco, Eduardo Geraldo

Note: please add your names and student numbers in all files you submit.
*/



/* There are auxiliary functions and lemmas to assist in the verification of the code below. */

import java.util.Random;
/*@
	fixpoint int sum(list<int> vs) {
		switch(vs) {
			case nil: return 0;
			case cons(h, t): return (h + sum(t));
		}
	}	
	
	lemma_auto(sum(append(xs, ys))) void sum_append(list<int> xs, list<int> ys)
	requires true;
	ensures sum(append(xs, ys)) == sum(xs) + sum(ys);
	{
		switch(xs) {
			case nil:
			case cons(h, t): sum_append(t, ys);
		}
	}	
		
	fixpoint int hashOf2(int h1, int h2) {
		return (h1^h2);
	}
	
	fixpoint int hashOf3(int h1, int h2, int h3) {
		return hashOf2(hashOf2(h1,h2),h3);
	}



	
@*/

/* These are the predicates defining representation invariants for the blockchain blocks and transactions. */
			
/*@	
	predicate isBlockchain(Blockchain b;) = b == null ? emp : b.head |-> ?l &*& isBlock(l,_);
 
	predicate isBlock(Block b;int h) = b == null ? h == 0 : b.BlockInv(_, _, h);

	predicate TransHash(unit a, Transaction t; int hash) =
		    t != null
		&*& TransInv(t, ?s, ?r, ?v)
		&*& hash == tansactionHash(s,r,v);
		
	fixpoint boolean ValidID(int id) {
		return 0 <= id && id < Block.MAX_ID;
	}

@*/

/* 
   The interface of the blockchain blocks. 

   It contains an instance predicate that is then defined in 
   two subclasses that define a summary block and a simple block. 
   
   This predicate defines the representation invariant for blockchain blocks.
   
*/

interface Block {
	//@ predicate BlockInv(Block p, int hp, int h); 

	static final int MAX_ID = 100;

	int balanceOf(int id);
	//@ requires BlockInv(?p, ?hp, ?h) &*& ValidID(id) == true;
	//@ ensures BlockInv(p, hp, h);

	Block getPrevious();
	//@ requires BlockInv(?p, ?hp, ?h);
	//@ ensures BlockInv(p, hp, h) &*& result == p;

	int getPreviousHash();
	//@ requires BlockInv(?p, ?hp, ?h);
	//@ ensures BlockInv(p, hp, h) &*& result == hp;

	int hash();
	//@ requires BlockInv(?p, ?hp, ?h);
	//@ ensures BlockInv(p, hp, h) &*& result == h;
}

/* 
   This class should be implemented in the course of the project 
   development with the expected operations to add and inspect the 
   blocks 
*/

class Blockchain {
	Block head;
	int counter; 
	
	public Blockchain()
	//@ requires true;
	//@ ensures isBlockchain(this) &*& this.counter |-> ?c &*& c == 0;
	{
	 head = null;
	 counter = 0;
	}
	// Add methods and fields here.
	
	public void addSummaryBlock(int balances[])
	//@ requires isBlockchain(this) &*& this.counter |-> ?c &*& c >= 0 &*& array_slice(balances,0,balances.length,_) &*& ValidCheckpoint(balances);
	//@ ensures isBlockchain(this);
	{ 
		counter++;
		
		if((counter % 10) != 0)
			return;
		else{
		//@assert counter % 10 == 0;
		
		SummaryBlock block = new SummaryBlock(head, 1, balances);
			
		head = block;	
		}	
	}
	
	public void addSimpleBlock(Transaction ts[])
	//@ requires isBlockchain(this) &*& this.counter |-> ?c &*& c >= 0 &*& array_slice_deep(ts,0,ts.length,TransHash,unit,_,_);
	//@ ensures isBlockchain(this);
	{
	counter++;
		
		if((counter % 10) == 0)
			return;
		else{
		//@assert counter % 10 != 0;
		
		SimpleBlock block = new SimpleBlock(head, 1, ts);
			
		head = block;	
		}
	}

	public static void main(String[] args) 
	//@ requires true;
	//@ ensures true;
	{
		int[] balances = new int[] { 70, 14 };

		Blockchain b = new Blockchain();
		

		Queue ts = new Queue(10);

		int paying = 50;
		
		Transaction t = new Transaction(balances[0], balances[1], paying);
		
		balances[0] -= paying;
		
		balances[1] += paying;

		ts.enqueue(t);

		//b.addSimpleBlock(ts.elements);

		b.addSummaryBlock(balances);
	}

}
	
	

