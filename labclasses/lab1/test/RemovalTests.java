import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

class RemovalTests {

    //XXX Requires JUnit 5

    private MyIntegerList generatedPopulatedList() {
        final MyIntegerList mil = new MyIntegerList();

        mil.push(1);
        mil.push(2);
        mil.push(1);
        mil.push(6);
        mil.push(6);
        mil.push(7);
        mil.push(2);
        mil.push(2);
        mil.push(0);
        mil.push(5);

        return mil;
    }

    @Test
    void testPop() {
        final MyIntegerList mil = generatedPopulatedList();
        assertEquals(10, mil.size());
        assertEquals("[1,2,1,6,6,7,2,2,0,5]", mil.toString());

        int elem = mil.pop();
        assertEquals(elem, 5);
        assertEquals(9, mil.size());
        assertEquals("[1,2,1,6,6,7,2,2,0]", mil.toString());

        elem = mil.pop();
        assertEquals(elem, 0);
        assertEquals(8, mil.size());
        assertEquals("[1,2,1,6,6,7,2,2]", mil.toString());

        elem = mil.pop();
        assertEquals(elem, 2);
        assertEquals(7, mil.size());
        assertEquals("[1,2,1,6,6,7,2]", mil.toString());

        for (int i = 0; i < 6; i++)
            mil.pop();

        elem = mil.pop();
        assertEquals(elem, 1);
        assertEquals(0, mil.size());
        assertEquals("[]", mil.toString());
    }

    @Test
    void testDequeue() {
        final MyIntegerList mil = generatedPopulatedList();
        assertEquals(10, mil.size());
        assertEquals("[1,2,1,6,6,7,2,2,0,5]", mil.toString());

        int elem = mil.dequeue();
        assertEquals(elem, 1);
        assertEquals(9, mil.size());
        assertEquals("[2,1,6,6,7,2,2,0,5]", mil.toString());

        elem = mil.dequeue();
        assertEquals(elem, 2);
        assertEquals(8, mil.size());
        assertEquals("[1,6,6,7,2,2,0,5]", mil.toString());

        elem = mil.dequeue();
        assertEquals(elem, 1);
        assertEquals(7, mil.size());
        assertEquals("[6,6,7,2,2,0,5]", mil.toString());

        for (int i = 0; i < 6; i++)
            mil.dequeue();

        elem = mil.dequeue();
        assertEquals(elem, 5);
        assertEquals(0, mil.size());
        assertEquals("[]", mil.toString());
        assertTrue(mil.isEmpty());
    }

    @Test
    void testRemoveAt() {
        final MyIntegerList mil = generatedPopulatedList();
        assertEquals(10, mil.size());
        assertEquals("[1,2,1,6,6,7,2,2,0,5]", mil.toString());

        mil.removeAt(1);
        assertEquals(9, mil.size());
        assertEquals("[1,1,6,6,7,2,2,0,5]", mil.toString());
    }

}