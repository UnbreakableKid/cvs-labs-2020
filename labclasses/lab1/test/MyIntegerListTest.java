import org.junit.Test;
import static org.junit.Assert.assertEquals;

public class MyIntegerListTest {


    @Test
    public void size() {
        MyIntegerList l = new MyIntegerList();
        l.push(1);
        assertEquals(1, l.size());

    }

    @Test
    public void push() {
        MyIntegerList l = new MyIntegerList();
        l.push(1);
        assertEquals(1, l.size());
        l.push(2);
        l.push(3);
        assertEquals(3, l.size());

    }

    @Test
    public void sortedInsertion() {
        MyIntegerList l = new MyIntegerList();
        l.push(3);
        l.push(6);
        l.push(1);
        l.sortedInsertion(5);
        assertEquals("[3,5,6,1]",l.toString());
    }

    @Test
    public void insertAt() {
        MyIntegerList l = new MyIntegerList();
        l.push(3);
        l.push(6);
        l.push(1);
        l.insertAt(2,1);
        assertEquals("[3,2,6,1]",l.toString());

    }

    @Test
    public void pop() {
    }

    @Test
    public void binaryIndex() {
        MyIntegerList l = new MyIntegerList();
        l.push(1);
        l.push(3);
        l.push(6);
        l.push(9);
        assertEquals(3, l.binaryIndex(9));
    }


    @Test
    public void dequeue() {
    }

    @Test
    public void indexOf() {
    }

    @Test
    public void bubbleSort() {
    }

    @Test
    public void elementsSum() {
    }

    @Test
    public void elementsAvg() {
    }

    @Test
    public void removeAt() {
    }

    @Test
    public void removeRepetitions() {
    }

    @Test
    public void isEmpty() {
    }

    @Test
    public void countDifferent() {
    }

    @Test
    public void testToString() {
    }
}
