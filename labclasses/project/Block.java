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
	
	public Block addSummaryBlock(int[] balances, int random)
	//@ requires isBlockchainWithCounter(this, ?c) &*& c >= 0 &*& array_slice(balances,0,balances.length,?elems) &*& balances.length == Block.MAX_ID &*& (c % 10 == 0);
	//@ ensures result != null ?isBlockchainWithCounter(this, c+1): isBlockchainWithCounter(this ,c);
	{


		//@close ValidCheckpoint(balances);
		SummaryBlock block = new SummaryBlock(head, random, balances);

		int hash = block.hash();
		int previousHash = block.hashPrevious;
		
		
		//@close isBlock(this.head, _);

		if((hash % 100 != 0)){
		
			return null;
		}
		
		
		//@close isBlock(block, hash);
		this.head = block;
		counter = counter + 1;
		//@close isBlock(this.head, _);
		return block;
		
	}	
	
	public Block addSimpleBlock(Transaction[] ts, int random)
	//@ requires isBlockchainWithCounter(this, ?c) &*& c > 0 &*& array_slice_deep(ts, 0, ts.length, TransHash, unit, _, _)  &*& (c % 10) != 0 &*& this.head |-> ?h &*& h.getClass() == SimpleBlock.class ? isBlock(h, _) : isBlock (h ,_ );
	//@ ensures result != null?isBlockchainWithCounter(this, c+1): isBlockchainWithCounter(this, c);
	{
		

		SimpleBlock block = new SimpleBlock(head, random, ts);

		int hash = block.hash();
				
		

		if((hash % 100 != 0)){
		
			return null;
		}
		
		
		//@close isBlock(block, hash);
		this.head = block;
		counter = counter + 1;
		//@close isBlock(this.head, _);
		return block;
	}


	
	public static void main(String[] args)
	//@ requires true;
	//@ ensures true;
	{

		int maxTransactions = 1;

		int[] balances = new int[Block.MAX_ID];


		for(int i = 0; i < Block.MAX_ID; i++)
		//@invariant  0 <= i &*& i <= balances.length &*& array_slice(balances, 0, Block.MAX_ID, _);
		
		{
			balances[i] = 0;
		}
		
		balances[0] = 100;
		
		Blockchain b = new Blockchain();


		
		int paying = 50;

		Transaction t = new Transaction(1, 0, paying);

		balances[0] -= paying;

		balances[1] += paying;


		Transaction[] toSend = new Transaction[maxTransactions];

		toSend[0] = t;
			

		int hash = 0;

		
		//@assert b.counter  == 0;
	
		int random = 1;
		
		//@close isBlockchain(b);
		
		//@assert array_slice(balances,0,balances.length,_);

		while(b.addSummaryBlock(balances, random) == null)
		//@ invariant isBlockchainWithCounter(b, 0);
		{
			
		random++;
		
		
		}
			
		
		//@assert b == null ? emp : b.head |-> ?l &*& isBlock(l,_) &*& b.counter |-> ?c;
		//@close isBlockchain(b);
		


					
	

		
	}
}

	
	

