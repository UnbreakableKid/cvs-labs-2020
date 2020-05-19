/*onstruction and Verification of Software 2019/20.

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
	predicate isBlockchain(Blockchain b;) = b == null ? emp : b.head |-> ?l &*& l != null &*& isBlock(l,_);
	
	predicate isBlockchainWithCounter(Blockchain b; int c) = isBlockchain(b) &*& b.counter |-> c &*& c >= 0;
 
	predicate isBlock(Block b;int h) = b == null ? h == 0 : b.BlockInv(_, _, h);

	predicate TransHash(unit a, Transaction t; int hash) =
		    t != null
		&*& TransInv(t, ?s, ?r, ?v)
		&*& hash == tansactionHash(s,r,v);
		
	fixpoint boolean ValidID(int id) {
		return 0 <= id && id < Block.MAX_ID;
	}
	
	predicate Positive(unit a, int v; unit n) = v >= 0 &*& n == unit;
	
	predicate isValidBalances(int[] balances, int size)=

		 array_slice_deep(balances, 0, size, Positive, unit, _,_);
	
@*/

/* 
   The interface of the blockchain blocks. 

   It contains an instance predicate that is then defined in 
   two subclasses that define a summary block and a simple block. 
   
   This predicate defines the representation invariant for blockchain blocks.
   
*/

interface Block {
	//@ predicate BlockInv(Block p, int hp, int h);

	static final int MAX_ID = 2;

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
 * This class should be implemented in the course of the project development
 * with the expected operations to add and inspect the blocks
 */

class Blockchain {
	Block head;
	int counter;
	

	public int getCounter() {
		return counter;
	}

	public Blockchain()
	//@ requires true;
	//@ ensures isBlockchain(this) &*& this.counter |-> ?c &*& c == 1;
	{
	
		
		int[] balances = new int[Block.MAX_ID];
		balances[0] = 100;
		//@close ValidCheckpoint(balances);
		SummaryBlock block = new SummaryBlock(null, 0, balances);
		head = block;
		counter = 1;
		//@close isBlock(head, _);
		

	}
	// Add methods and fields here.

	public SummaryBlock addSummaryBlock(Block x, int[] balances, int random)
	/*@ requires isBlockchainWithCounter(this, ?c)&*& c >= 0 &*&
	array_slice(balances,0,balances.length,_) 
	&*& balances.length == Block.MAX_ID
	&*& (c == 0? (c == 0):(c % 10 == 0))
	&*& x != null
	&*& isBlock(x, _);
	
	@*/
	
	/*@ ensures result == null? isBlockchainWithCounter(this, c): isBlockchainWithCounter(this, c+1);@*/
	{
		//@close ValidCheckpoint(balances);

		SummaryBlock block = new SummaryBlock(x, random, balances);


		if (block.hash() % 100 != 0) {

		//@ open isBlock(block, _);
		return null;
			
		}

	
		this.head = block;
			counter = counter + 1;

			//@close isBlock(head, _);
			return block;


	}

	public void addSimpleBlock(Transaction[] ts, int random)
	/*@ requires isBlockchainWithCounter(this, ?c) 
	&*& array_slice_deep(ts,0,ts.length,TransHash,unit,_,_)
	&*& (c % 10 != 0);
	@*/ 
	/*@ ensures isBlockchainWithCounter(this, c+1); @*/
	{

		//@open isBlockchainWithCounter(this,c);
		//@open isBlockchain(this);
		//@open isBlock(this.head,_);

		SimpleBlock block = new SimpleBlock(head, random, ts);

		while (block.hash() % 100 != 0)
		//@ invariant block != null;
		{

			random++;
			block = new SimpleBlock(head, random, ts);
		}

		this.head = block;
		counter = counter + 1;

		//@close isBlock(head, _);
		return block;

	}
	
	
	// public Transaction doTransaction(Block head, int sender, int receiver, int amount)
	// //@requires isBlockchain(this) &*& isBlock(head,_) &*& amount > 0 &*& ValidID(sender) == true &*& ValidID(receiver) == true &*& head != null;
	// //@ensures result == null? TransInv(result, sender, receiver, 0): TransInv(result, sender, receiver, amount);  
	// {

	// 	int balanceOfSender = 0;
		
	// 	//@open isBlock(head, _);
	// 	while ((head instanceof SimpleBlock) && head != null)
	// 	//@ invariant true; 
	// 	{

	// 		//@close isBlock(head, _);
	// 		balanceOfSender += head.balanceOf(sender);
			
	
	// 		head = head.getPrevious();

	// 		//@close isBlock(head, _);
	// 	}
		

	// 	balanceOfSender += head.balanceOf(sender);

	// 	if (balanceOfSender < 0) {
			
	// 		Transaction t = new Transaction(sender, receiver, 0);
			
	// 		return t;
	// 	}
	// 	//@assert amount > 0;
	// 	Transaction t = new Transaction(sender, receiver, amount);

	// 	return t;
	// }

	public static void main(String[] args)
	//@ requires true;
	//@ ensures true;
	{

		int maxTransactions = 1;

		int[] balances = new int[Block.MAX_ID];

		int counter = 0;

		balances[0] = 100;
		balances[1] = 50;
		

		
		Blockchain b = new Blockchain();

		int paying = 50;

		//Transaction t = doTransaction(b.head, 1, 0, paying);
		
		//@ assert array_slice_deep(balances, 0, Block.MAX_ID, Positive, unit, _,_);
		
		//balances[0] -= paying;
		
		//balances[1] += paying;
		
		//@ assert array_slice_deep(balances, 0, Block.MAX_ID, Positive, unit, _,_);
		
		//b.inspectBlock(b.head, 1);

		
		//@assert b.counter == 1;
		int random = 0;
		
		//@assert b.counter == 1;
		
		//@ assert array_slice_deep(balances, 0, Block.MAX_ID, Positive, unit, _,_);
		
		//@open isBlockchainWithCounter(b,1);
		
				//@ assert array_slice_deep(balances, 0, Block.MAX_ID, Positive, unit, _,_);
				
				Transaction t = new Transaction( 1, 0, paying);
		
		Transaction[] toSend = new Transaction[maxTransactions];
		
				
		toSend[0] = t;
		Block tmp = b.head;
		 
		b.addSimpleBlock(toSend, random);
		
			
		while (b.addSummaryBlock(b.head, balances, random) == null)
		/*@invariant isBlockchainWithCounter(b, 1) 
		&*& isValidBalances(balances, Block.MAX_ID);@*/
		{
		random++;
		}
		//@close isBlockchain(b);
		
		////@assert b.counter == 1;
		
		
		
	}
}
