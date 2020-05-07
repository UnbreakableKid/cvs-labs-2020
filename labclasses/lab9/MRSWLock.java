/* For this lab, you'll have to implement and verify  a readers-writer lock,
   also known as a multiple readers single writer lock. As the name implies,
   multiple readers can acquire the lock with reading rights, however, it can
   only be held by one writer. Furthermore, it if the lock has been acquired for
   reading, it cannot be acquired for writing and vice-versa.
*/

class MRSWLock {
	
	/* 
	 * Aquires this lock for reading, after successfully returned from this
	 * method, the caller has reading rights on the state protected by this
	 * lock.
	 */
	public void readLock ();
	
	/* 
	 * Releases the reading lock.
	 */
	void readUnlock ();
	
	/*
	 * Acquires this lock for writing, after successfully returned from this
	 * method, the caller has writing rights on the state protected by this
	 * lock.
	 */
	void writeLock ();

	/*
	 * Releases the writing lock.
	 */
	void writeUnlock ();
}
