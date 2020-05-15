/*
Construction and Verification of Software 2019/20.

Project assignment to implement and verify a simplified blockchain.

�2020 Jo�o Costa Seco, Eduardo Geraldo

Note: please add your names and student numbers in all files you submit.
*/


/* There are auxiliary functions and lemmas to assist in the verification of the code below. */


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
	
	predicate isBlockchainWithCounter(Blockchain b; int c) = isBlockchain(b) &*& b.counter |-> c &*& c >= 0;
 
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
	
	public int getCounter(){
		return counter;
		}

	public Blockchain()
	//@ requires true;
	//@ ensures isBlockchain(this) &*& this.counter |-> ?c &*& c == 0;
	{
		head = null;
		counter = 0;

	}
	// Add methods and fields here.

	public void addSummaryBlock(int[] balances, int hash)
	//@ requires isBlockchainWithCounter(this, ?c) &*& c >= 0 &*& array_slice(balances,0,balances.length,_) &*& balances.length == Block.MAX_ID &*& (c == 0? (c == 0):(c % 10 == 0));
	//@ ensures isBlockchainWithCounter(this, c+1);
	{

		

		//@close ValidCheckpoint(balances);
		SummaryBlock block = new SummaryBlock(head, hash, balances);
		head = block;
		counter = counter + 1;
	}

	

	public void addSimpleBlock(Transaction[] ts, int hash)
	//@ requires isBlockchainWithCounter(this, ?c)&*& c >= 0 &*& array_slice_deep(ts, 0, ts.length, TransHash, unit, _, _)  &*& (c == 1? (c == 1):(c % 10 != 0));
	//@ ensures isBlockchainWithCounter(this, c+1);
	{




		SimpleBlock block = new SimpleBlock(head, hash, ts);

		head = block;
		//@close isBlockchain(this);
		counter++;

	}

	public static void main(String[] args)
	//@ requires true;
	//@ ensures true;
	{

		int maxTransactions = 1;

		int[] balances = new int[Block.MAX_ID];

		balances[0] = 100;
		balances[1] = 0;
		balances[2] = 0;
		balances[3] = 0;
		balances[4] = 0;

		Blockchain b = new Blockchain();

		//Queue ts = new Queue(100);

		int paying = 50;

		Transaction t = new Transaction(1, 0, paying);

		balances[0] -= paying;

		balances[1] += paying;

		//ts.enqueue(t);
		//ts.enqueue(t);
		//ts.enqueue(t);
		//ts.enqueue(t);
		//ts.enqueue(t);

		Transaction[] toSend = new Transaction[maxTransactions];


		//for queue on second phase	

		//int i = 0;

		//while (i < maxTransactions)
		////@ invariant QueueInv(ts,?x,?m) &*& m >= maxTransactions &*& x > 0 &*& i >= 0  &*& array_slice(toSend,0,toSend.length, _);


		toSend[0] = t;
		
		

		int hash = 0;
		int random = 0;
		
		//@assert b.counter  == 0;
		b.addSummaryBlock(balances, random);

		if (b.head != null) {
			hash = b.head.hash();
			random = hash ^ (hash & 3);	
			
			//@assert b == null ? emp : b.head |-> ?l &*& isBlock(l,_) &*& b.counter |-> ?c;
			//@close isBlockchain(b);
			
			//@assert b.counter  == 1;

			
			b.addSimpleBlock(toSend, random);



			//hash = b.head.hash();

			//get last two 00s
			//random = hash ^ (hash & 3);		

		}
	}
}

	
	

