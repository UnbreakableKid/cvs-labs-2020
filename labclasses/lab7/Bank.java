/*
Starting point for exercise of Lab Session 7.
CVS course - Integrated Master in Computer Science and Engineering
@FCT UNL Luis Caires 2015
*/


class Bank {

    BankAccount store[];
    int nelems;
    int capacity;

    /*
     * Constructor. Given a size as parameter, initializes the underlying array.
     */
    public Bank(int size) {}

    /*
     * Creates and stroes a new account with the id code.
     */
    void addnewAccount(int code) {}

    /*
     * This operation returns the balance of the account with id code. If the
     * account with id code does not exist, the method returns -1.
     */
    int getbalance(int code) {}

    /*
     * Removes the account with the id code from this Bank.
     * This operation retuns a boolean indicating whether or not
     * the account was successfully removed.
     */
    boolean removeAccount(int code) {}

    /*
     * This operation transfers val from the account with the id from to the
     * account with the id to.
     * The return of the oiperation shows whether or not the transaction
     * processed successfully.
     */
    boolean transfer(int from, int to, int val) {} 

    /*
     * Operation responisble for the expansion of the array in oreder to
     * accommodate a greater number of accounts.
     */
    void extendstore() {}

}
