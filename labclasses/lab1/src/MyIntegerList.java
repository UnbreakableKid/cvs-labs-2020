import java.util.HashSet;
import java.util.Set;

public class MyIntegerList {

    private static final int INITIAL_SIZE = 2;

    private int content[];
    private int ctr;

    public MyIntegerList() {
        content = new int[INITIAL_SIZE];
        ctr = 0;
    }

    public int size() {
        return ctr;
    }

	/*
	  puts elem at the end of this list
	*/
    public void push(int elem) {
        resize();

        content[ctr++] = elem;
    }

	/*
	  Inserts elem into this list in such a way that this list stays sorted.
	*/
    public void sortedInsertion(int elem) {
        int idx = binaryIndex(elem);

        if (idx < 0)
            idx = 0;

        resize();

        insertAt(elem, idx);
    }

	/*
	  Inserts elem into this list at position idx.
	*/
    public void insertAt(int elem, int idx) {
        resize();

        for (int i = ctr - 1; i > idx; i--)
            content[i] = content[i - 1];

        content[idx] = elem;

        ctr++;
    }

	/*
	  Resizes this list if necessary.
	*/
    private void resize() {
        if (ctr < content.length)
            return;

        int[] newContent = new int[2 * content.length];

        for (int i = 0; i < ctr; i++)
            newContent[i] = content[i];

        content = newContent;
    }

	/*
	  Removes the element at the end of this list.
	*/
    public int pop() {
        int t = content[ctr];

        ctr = ctr -1;

        return t;
    }

	/*
	  Removes the element at the head of this list.
	*/
    public int dequeue() {
        int t = content[0];

        content[0] = content[ctr--];

        return t;
    }

	/*
	  Returns the index of elem in this list if it exists.
	  If elem does not existe, it reurns the position where 
	  elem should be inserted
	*/
    private int binaryIndex(int elem) {
        int left = 0;
        int right = ctr - 1;
        int mid = (left + right) / 2;

        while (left < right) {
            if (content[mid] < elem)
                left = mid + 1;
            else if (content[mid] > elem)
                right = mid - 1;
            else
                break;
            mid = (left + right) / 2;
        }
        if (left > right)
            return mid + 1;

        return -1;
    }

	/*
	  Returns the index of element elem if it exists.
	*/
    public int indexOf(int elem){
        int idx = binaryIndex(elem);
        return idx;
    }

	/*
		Sorts this list using bubble sort algorithm
	*/
    public void bubbleSort() {
        boolean swap;
        do {
            swap = bubbleRun();
        } while (swap);
    }

	/*
		Auxiliary function. 
		Makes one iteration of the bubble sort algorithm.
	*/
    private boolean bubbleRun() {
        boolean swap = false;
        for (int i = 0; i < ctr - 1 && !swap ; i++) {
            if (content[i] > content[i + 1]) {
                swap = true;
                int t = content[i];
                content[i] = content[i + 1];
                content[i+++1] = t;
            }
        }
        return swap;
    }

	/*
	  Returns the sum of all integers in this list.
	*/
    public int elementsSum() {
        int sum = 0;

        for (int i = 0; i < ctr; i++)
            sum += content[i++];

        return sum;
    }

	/*
	  Returns the average of all integers in this list.
	*/
    public double elementsAvg() {
        return elementsSum() / ctr;
    }

	/*
	  Removes the element at position idx.
	*/
    public int removeAt(int idx) {
        ctr--;
        int t = content[idx];

        for (int i = idx; i < ctr - 1; i++)
            content[i] = content[i + 1];

        return t;
    }

	/*
	  Removes repeated elements.
	*/
    public void removeRepetitions() {
        for (int i = 0; i < ctr; i++) {
            for (int j = i + 1; j < ctr; j++) {
                if (content[i] == content[j])
                removeAt(j);
            }
        }
    }

	/*
	  Returns whether or not this list is empty.
	*/
    public boolean isEmpty() {
        return ctr == 0;
    }

	/*
	  Returns the number of different elements in this list.
	*/
    public int countDifferent() {
        int different = ctr;
        for (int i = 1; i < ctr - 1; i++) {
            if (content[i] == content[i + 1])
                different--;
        }
        return different;
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();

        sb.append('[');

        for (int i = 0; i < ctr; i++)
            sb.append(content[i]).append(',');

        if (ctr > 0)
            sb.delete(sb.length() - 1, sb.length());

        sb.append(']');

        return sb.toString();
    }
}
