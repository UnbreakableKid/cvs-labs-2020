/*Construction and Verification of Software 2019/20.

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

	final static int simpleToSummaryRatio = 3;
	final static int blocksToCreate = 4; // counter ends at blocksToCreate + 1 (we create a summary right at the constructor)

	Block head;
	int counter;
	

	public int getCounter() 
	//@ requires isBlockchainWithCounter(this, ?c);
	//@ ensures result == c &*& isBlockchainWithCounter (this, c);
	{
		return counter;
	}

	public Blockchain()
	//@ requires true;
	//@ ensures isBlockchainWithCounter(this, 1);
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



	public boolean addSummaryBlock(SummaryBlock b)
		/*@ requires
		this.counter |-> ?c	
		&*& this.head |-> ?h
		&*& b.BlockInv(h, _,_)
		&*& h != null
		&*& c > 0
		;
		@*/
		//@ ensures result == true? isBlockchainWithCounter(this, c+1) : isBlockchainWithCounter(this, c);
		{
					
		if (b.hash() % 100 != 0) {
			//@open b.BlockInv(h, _,_);
			//@close isBlockchainWithCounter(this, c);
			return false;
		}
		this.head = b;
		this.counter++;
		return true;	
		}

	public boolean addSimpleBlock(SimpleBlock b)
		/*@ requires	this.counter |-> ?c	
		&*& this.head |-> ?h
		&*& b.BlockInv(h, _,_)
		&*& h != null
		&*& c > 0
		;
			@*/
			//@ ensures result == true? isBlockchainWithCounter(this, c+1) : isBlockchainWithCounter(this, c);
	{

		if (b.hash() % 100 != 0) {

		//@open b.BlockInv(h, _,_);
		//@close isBlockchainWithCounter(this, c);
			return false;
		}
		this.head = b;
		this.counter++;
		return true;
	}

	public static void main(String[] args)
	//@ requires [_] System.out |-> ?o &*& o != null;
	//@ ensures true;
	{

		int maxTransactions = 1;

		int[] balances = new int[Block.MAX_ID];

	
		Blockchain b = new Blockchain();

		int paying = 50;

		//Transaction t = doValidTransaction(b.head, 1, 0, paying);
	
				
		Transaction t = new Transaction( 1, 0, paying);
		
		Transaction[] toSend = new Transaction[maxTransactions];
		
	
				
		toSend[0] = t;
		int random = 0;
		int i = 0;
		while(i <= blocksToCreate)
		//@invariant i >= 0 &*& i <= blocksToCreate+1 &*& isBlockchainWithCounter(b, ?c) &*& c > 0 &*& array_slice_deep(toSend,0,toSend.length,TransHash,unit,_,_) &*& array_slice(balances, 0, balances.length,_)  &*& [_] System.out |-> o &*& o != null;
		{	
			
			
			if (b.getCounter() % simpleToSummaryRatio != 0) {
				
				
				SimpleBlock block = new SimpleBlock(b.head, random, toSend);
				System.out.print("Adding SimpleBlock... ");
				if(b.addSimpleBlock(block)){
					System.out.println("Success");
					i++;
				}
				else
					System.out.println("Failed");

			}
			else
			{
				
				//@close ValidCheckpoint(balances);
				SummaryBlock block = new SummaryBlock(b.head, random, balances);	
				System.out.print("Adding SummaryBlock... ");
						
				
				if(b.addSummaryBlock(block)){
					System.out.println("Success");
					i++;
				}
				else
					System.out.println("Failed");
			}
			random++;
		}
		
	}

	// public SummaryBlock createSummaryBlock(Block x, int[] balances, int random)
	// /*@ requires isBlockchainWithCounter(this, ?c) &*& c >= 0 &*&
	// array_slice(balances,0,balances.length,_) 
	// &*& balances.length == Block.MAX_ID
	// &*& (c == 0 || c == 10)
	// &*& x != null
	// &*& isBlock(x, _);
	
	// @*/
	
	// /*@ ensures isBlock(result, _ ); @*/
	// {
	// 	//@close ValidCheckpoint(balances);

	// 	SummaryBlock block = new SummaryBlock(head, random, balances);

	
	// 	return block;


	// }

	// public Block createSimpleBlock(Transaction[] ts, int random)
	// /*@ requires isBlockchainWithCounter(this, ?c) 
	// &*& array_slice_deep(ts,0,ts.length,TransHash,unit,_,_)
	// &*& c  > 0 &*& c < 10;
	// @*/ 
	// /*@ ensures result == null? isBlockchainWithCounter(this, c) : isBlockchainWithCounter(this, c+1); @*/
	// {


	// 	SimpleBlock block = new SimpleBlock(head, random, ts);


	// 	this.head = block;
	// 	counter = counter + 1;
	// 	return block;

	// }
	
	
	// public Transaction doValidTransaction(Block head, int sender, int receiver, int amount)
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

	
}
