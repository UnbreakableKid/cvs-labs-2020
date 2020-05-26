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

final class Blockchain {

	final static int simpleToSummaryRatio = 10;
	final static int blocksToCreate = 20; // counter ends at blocksToCreate + 1 (we create a summary right at the constructor)

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

	public int[] getBalances(SimpleBlock block)
	//@requires block != null &*& isBlock(block,?h);
	//@ensures isBlock(block,h) &*& array_slice(result, 0, result.length, _) &*& ValidCheckpoint(result) &*& result.length == Block.MAX_ID;
	{
		Block previous = block.getPrevious();
		int[] balances = new int[Block.MAX_ID];

		if (previous != null) {
			if (previous instanceof SummaryBlock) {

				//@open block.BlockInv(previous,?h2,_);

				for (int i = 0; i < balances.length; i++)
				//@invariant array_slice(balances, 0, Block.MAX_ID, _) &*& 0 <= i &*& i <= Block.MAX_ID &*& isBlock(previous, h2);
				{

					balances[i] = previous.balanceOf(i);
				}

				//@close ValidCheckpoint(balances);
				return balances;
			} else if (previous instanceof SimpleBlock) {
				//@open block.BlockInv(previous,_,_);
				balances = getBalances((SimpleBlock) previous);

			}
		}

		for (int j = 0; j < balances.length; j++)
		//@invariant array_slice(balances, 0, Block.MAX_ID, _) &*& isBlock(block, h) &*& j >= 0 &*& j <= Block.MAX_ID;
		{

			balances[j] = block.balanceOf(j);
		}

		//@close ValidCheckpoint(balances);
		return balances;
	}

	public boolean addSummaryBlock(SummaryBlock b)
	/*@ requires
	this.counter |-> ?c	
	&*& this.head |-> ?h
	&*& b.BlockInv(h, _,_)
	&*& h != null
	&*& c> 0
	&*& c % simpleToSummaryRatio == 0;
	
	@*/
	//@ ensures result == true? isBlockchainWithCounter(this, c+1): isBlockchainWithCounter(this, c);
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
	&*& c >= 0;
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

	public boolean createSimpleBlock(int random, Transaction[] ts)
	//@requires random >= 0 &*& ts != null &*& isBlockchainWithCounter(this, ?c) &*& c >= 0  &*& array_slice_deep(ts,0,ts.length,TransHash,unit,_,_) &*& [_] System.out |-> ?o &*& o != null;
	//@ensures true;
	{
		
				SimpleBlock block = new SimpleBlock(head, random, ts);

				System.out.print("Adding SimpleBlock... ");
				if (addSimpleBlock(block)) {
					System.out.println("Success");
					return true;
				} else {
					System.out.println("Failed");
					return false;
				}
	}
	public static void main(String[] args)
	//@ requires [_] System.out |-> ?o &*& o != null;
	//@ ensures true;
	{

		int maxTransactions = 2;

		int[] balances = new int[Block.MAX_ID];

		Blockchain b = new Blockchain();

		int paying = 50;

		Transaction t = new Transaction(1, 0, paying);
		Transaction t3 = new Transaction(0, 1, paying);

		Transaction[] toSend = new Transaction[maxTransactions];

		CQueue queue = new CQueue(21);

		TransactionMaker tm = new TransactionMaker(queue, Block.MAX_ID);

		SimpleBlockMaker simp = new SimpleBlockMaker(b,queue, maxTransactions);
//		SummaryBlockMaker summ = new SummaryBlockMaker(b);

		// toSend[0] = t;
		// //@ array_slice_deep_close(toSend,0, TransHash, unit);
		// toSend[1] = t3;
		// //@ array_slice_deep_close(toSend,1, TransHash, unit);
		// int random = 0;
		// int i = 0;
		// while (i <= blocksToCreate)
		// /*@invariant i >= 0 &*& i <= blocksToCreate+1 &*& isBlockchainWithCounter(b, ?c) &*& c > 0 
		// &*& array_slice(balances, 0, balances.length, _) &*& balances.length == Block.MAX_ID &*& array_slice_deep(toSend,0,toSend.length,TransHash,unit,_,_) &*& [_] System.out |-> o &*& o != null;
		// @*/
		// {

		// 	if (b.getCounter() % simpleToSummaryRatio != 0) {

		// 		SimpleBlock block = new SimpleBlock(b.head, random, toSend);

		// 		toSend = new Transaction[maxTransactions];

		// 		System.out.print("Adding SimpleBlock... ");
		// 		if (b.addSimpleBlock(block)) {
		// 			System.out.println("Success");
		// 			i++;
		// 		} else {
		// 			System.out.println("Failed");
		// 		}

		// 		//just for simulation purposes
		// 		Transaction t1 = new Transaction(1, 0, paying);
		// 		Transaction t2 = new Transaction(0, 1, paying);
		// 		toSend[0] = t1;
		// 		//@ array_slice_deep_close(toSend,0, TransHash, unit);
		// 		toSend[1] = t2;
		// 		//@ array_slice_deep_close(toSend,1, TransHash, unit);
		// 	} else {

		// 		System.out.println("Fetching balances... ");
		// 		//@open isBlockchainWithCounter(b, _);
		// 		//@open isBlockchain(b);
		// 		//@close isBlock(b.head,_);

		// 		//@close ValidCheckpoint(balances);
		// 		SummaryBlock block = new SummaryBlock(b.head, random, balances);

		// 		System.out.print("Adding SummaryBlock... ");

		// 		if (b.addSummaryBlock(block)) {
		// 			System.out.println("Success");
		// 			balances = new int[Block.MAX_ID];

		// 			for (int j = 0; j < balances.length; j++)
		// 			//@invariant array_slice(balances, 0, Block.MAX_ID, _) &*& 0 <= j &*& j <=  balances.length &*& isBlockchain(b);
		// 			{

		// 				balances[j] = b.head.balanceOf(j);
		// 			}
		// 			i++;
		// 		} else {
		// 			System.out.println("Failed");

		// 			balances = new int[Block.MAX_ID];

		// 			balances = b.getBalances((SimpleBlock) b.head);
		// 		}
		// 	}
		// 	random++;

		// }

	}
}


/**
 * SimpleBlockMaker
 */

/*@ predicate SimpInv(SimpleBlockMaker tm;) = tm.blockchain |-> ?b &*& isBlockchainWithCounter(b,?c) &*& c>=0 &*& b!=null &*& tm.queue |-> ?q &*& q != null 

&*& CQueueInv(q)
&*& tm.maxTransactions |-> ?m &*& m > 0;

@*/
class SimpleBlockMaker implements Runnable {

	Blockchain blockchain;
	CQueue queue;
	int maxTransactions;
	//@predicate pre() = SimpInv(this);
	//@predicate post() = true;

	public SimpleBlockMaker(Blockchain b, CQueue q, int maxTransactions)
	//@requires isBlockchainWithCounter(b,?c) &*& c>=0 &*& b!=null &*& q != null &*& CQueueInv(q) &*& maxTransactions > 0;
	//@ensures pre();
	{
		this.blockchain = b;
		this.queue = q;
		this.maxTransactions = maxTransactions;

	}

	public void run()
	//@requires pre();
	//@ensures post();
	{
		int random = 0;
		while (true)
		//@invariant SimpInv(this) &*& random >=0;
		{
			
			Transaction[] ts = new Transaction[maxTransactions];

			for (int i = 0; i < maxTransactions; i++)
			//@invariant this.maxTransactions |-> ?t &*& this.queue |-> ?q &*& CQueueInv(q) &*& q!=null &*& array_slice(ts,0,t,_) &*& 0 <= i &*& i<= ts.length;
			{
				Transaction temp = queue.dequeue();
				//@close [1]TransHash(unit,temp,_);
				ts[i] = temp;
				//@ array_slice_deep_close(ts, i, TransHash, unit);
			}
			//@ assert array_slice_deep(ts,0,ts.length,TransHash,unit,_,_);
			if (!blockchain.createSimpleBlock(random, ts))
				for (int i = 0; i < ts.length; i++) {
					queue.enqueue(ts[i]);
				}

			random++;

		}
	}

}

/*@ predicate TmInv(TransactionMaker tm;) = tm.queue |-> ?q 
&*& q != null &*& CQueueInv(q) &*& tm.clients |-> ?c 
&*& c == Block.MAX_ID;

@*/
class TransactionMaker implements Runnable{
	CQueue queue;
	int clients;
	//@predicate pre() = TmInv(this);
	//@predicate post() = true;

	public TransactionMaker(CQueue q, int clients) 
		//@requires q!=null &*& CQueueInv(q) &*& clients == Block.MAX_ID;
		//@ensures pre() &*& CQueueInv(q);
		{
		this.queue = q;
		this.clients = clients;

	 	}
 
	public void run()
	//@requires pre();
	//@ensures post();
	{
		int counter = 0;
		while (true) 
		//@invariant TmInv(this);
		{
			// try {
				//Thread.sleep(3000);
				Transaction transaction = new Transaction(0, 1, 50);
			
			// } catch (InterruptedException e) {
			// 	e.printStackTrace();
			// }
		}
	 
 	}

}
	
	// public Transaction doValidTransaction(int sender, int receiver, int amount)
	// //@requires isBlockchain(this) &*& isBlock(head,_) &*& amount > 0 &*& ValidID(sender) == true &*& ValidID(receiver) == true &*& head != null;
	// //@ensures result == null? TransInv(result, sender, receiver, 0): TransInv(result, sender, receiver, amount);  
	// {

	// 	int balanceOfSender = 0;
		
	// 	int[] balances = getBalances();
		

	// 	balances[sender] += head.balanceOf(sender);

	// 	if (balanceOfSender < 0) {
						
	// 		return null;
	// 	}
	// 	//@assert amount > 0;
	// 	Transaction t = new Transaction(sender, receiver, amount);

	// 	return t;
	// }

	

