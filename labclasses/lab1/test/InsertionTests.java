import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;

public class InsertionTests {

    //XXX Requires JUnit 5

    @Test
    public void testPush() {
        final MyIntegerList mil = new MyIntegerList();

        assertEquals(0, mil.size());
        assertEquals("[]", mil.toString());

        mil.push(1);
        assertEquals(1, mil.size());
        assertNotEquals("[]", mil.toString());
        assertEquals("[1]", mil.toString());

        mil.push(2);
        assertEquals(2, mil.size());
        assertEquals("[1,2]", mil.toString());

        mil.push(1);
        assertEquals(3, mil.size());
        assertEquals("[1,2,1]", mil.toString());
    }


    @Test
    public void testInsertAt() {
        final MyIntegerList mil = new MyIntegerList();

        assertEquals(0, mil.size());
        assertEquals("[]", mil.toString());

        mil.insertAt(9, 0);
        assertEquals(1, mil.size());
        assertEquals("[9]", mil.toString());

        mil.insertAt(8, 0);
        assertEquals(2, mil.size());
        assertEquals("[8,9]", mil.toString());

        mil.insertAt(10, 1);
        assertEquals(3, mil.size());
        assertEquals("[8,10,9]", mil.toString());

        mil.insertAt(15, 3);
        assertEquals(4, mil.size());
        assertEquals("[8,10,9,15]", mil.toString());
    }

    @Test
    public void testSortedInsertion() {
        final MyIntegerList mil = new MyIntegerList();

        assertEquals(0, mil.size());
        assertEquals("[]", mil.toString());

        mil.sortedInsertion(0);
        assertEquals(1, mil.size());
        assertEquals("[0]", mil.toString());

        mil.sortedInsertion(-1);
        assertEquals(2, mil.size());
        assertEquals("[-1,0]", mil.toString());

        mil.sortedInsertion(-1);
        assertEquals(3, mil.size());
        assertEquals("[-1,-1,0]", mil.toString());

        mil.sortedInsertion(5);
        assertEquals(4, mil.size());
        assertEquals("[-1,-1,0,5]", mil.toString());

        mil.sortedInsertion(6);
        assertEquals(5, mil.size());
        assertEquals("[-1,-1,0,5,6]", mil.toString());

        mil.sortedInsertion(3);
        assertEquals(6, mil.size());
        assertEquals("[-1,-1,0,3,5,6]", mil.toString());

        mil.sortedInsertion(-1);
        assertEquals(7, mil.size());
        assertEquals("[-1,-1,-1,0,3,5,6]", mil.toString());

        mil.sortedInsertion(-2);
        assertEquals(8, mil.size());
        assertEquals("[-2,-1,-1,-1,0,3,5,6]", mil.toString());

        mil.sortedInsertion(0);
        assertEquals(9, mil.size());
        assertEquals("[-2,-1,-1,-1,0,0,3,5,6]", mil.toString());

        mil.sortedInsertion(2);
        assertEquals(10, mil.size());
        assertEquals("[-2,-1,-1,-1,0,0,2,3,5,6]", mil.toString());
    }
}