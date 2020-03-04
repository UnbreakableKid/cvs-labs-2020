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

    public void push(int elem) {
        resize();

        content[ctr++] = elem;
    }

    public void sortedInsertion(int elem) {
        int idx = binaryIndex(elem);

        if (idx < 0)
            idx = 0;

        resize();

        insertAt(elem, idx);
    }

    public void insertAt(int elem, int idx) {
        resize();

        for (int i = ctr - 1; i > idx; i--)
            content[i] = content[i - 1];

        content[idx] = elem;

        ctr++;
    }

    private void resize() {
        if (ctr < content.length)
            return;

        int[] newContent = new int[2 * content.length];

        for (int i = 0; i < ctr; i++)
            newContent[i] = content[i];

        content = newContent;
    }

    public int pop() {
        int t = content[ctr];

        ctr = ctr -1;

        return t;
    }

    public int dequeue() {
        int t = content[0];

        content[0] = content[ctr--];

        return t;
    }

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

        if(left == right)
            return mid + 1;
        return mid;
    }

    public int indexOf(int elem){
        int idx = binaryIndex(elem);
        return idx;
    }

    public void bubbleSort() {
        boolean swap;
        do {
            swap = bubbleRun();
        } while (swap);
    }

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

    public int elementsSum() {
        int sum = 0;

        for (int i = 0; i < ctr; i++)
            sum += content[i++];

        return sum;
    }

    public double elementsAvg() {
        return elementsSum() / ctr;
    }

    public int removeAt(int idx) {
        ctr--;
        int t = content[idx];

        for (int i = idx; i < ctr - 1; i++)
            content[i] = content[i + 1];

        return t;
    }

    public void removeRepetitions() {
        for (int i = 0; i < ctr; i++) {
            for (int j = i + 1; j < ctr; j++) {
                if (content[i] == content[j])
                removeAt(j);
            }
        }
    }

    public boolean isEmpty() {
        return ctr == 0;
    }

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
