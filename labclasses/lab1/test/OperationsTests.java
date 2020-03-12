import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

class OperationsTests {

    //XXX Requires JUnit 5


    private static void assertBetween(int expectedLower, int expectedUpper, int actual) {
        assertTrue(expectedLower <= actual && expectedUpper >= actual);
    }

    private MyIntegerList generatedPopulatedList(){
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
        mil.push(10);

        return mil;
    }

    @Test
    void TestBinSrch1() {
        MyIntegerList mil = new MyIntegerList();
        for (int i = 0; i < 10; i++)
            mil.push(i);
        assertEquals(10, mil.size());
        assertEquals("[0,1,2,3,4,5,6,7,8,9]", mil.toString());

        assertEquals(0, mil.binaryIndex(-1));
        assertBetween(1, 2, mil.binaryIndex(1));
        assertEquals(10, mil.binaryIndex(10));

        for(int i = 0; i < 5; i++)
            mil.insertAt(-1, 5);

        assertEquals(15, mil.size());
        assertEquals("[0,1,2,3,4,-1,-1,-1,-1,-1,5,6,7,8,9]", mil.toString());

        assertNotEquals(5, mil.binaryIndex(-1));
        assertNotEquals(6, mil.binaryIndex(-1));
        assertEquals(7, mil.binaryIndex(-1)); //In this case the binary search will return the index 7
        assertNotEquals(8, mil.binaryIndex(-1));//but it could return any index between 5 and 9 as it
        assertNotEquals(9, mil.binaryIndex(-1));//would be correct!

        //hence we use an auxiliary assertion (defined above):
        assertBetween(5, 9, mil.binaryIndex(-1));
    }

    @Test
    void testSort() {
        final MyIntegerList mil = generatedPopulatedList();
        assertEquals(11, mil.size());
        assertEquals("[1,2,1,6,6,7,2,2,0,5,10]", mil.toString());


        mil.bubbleSort();
        assertEquals(11, mil.size());
        assertEquals("[0,1,1,2,2,2,5,6,6,7,10]", mil.toString());
    }

    @Test
    void testSum(){
        final MyIntegerList mil = generatedPopulatedList();
        assertEquals(11, mil.size());
        assertEquals("[1,2,1,6,6,7,2,2,0,5,10]", mil.toString());

        assertEquals(42, mil.elementsSum());
    }

    @Test
    void testAvg(){
        final MyIntegerList mil = generatedPopulatedList();
        assertEquals(11, mil.size());
        assertEquals("[1,2,1,6,6,7,2,2,0,5,10]", mil.toString());
        mil.pop();

        assertEquals(32, mil.elementsSum());

        assertEquals(3.2, mil.elementsAvg());
    }

    @Test
    void testCountDiff(){
        final MyIntegerList mil = new MyIntegerList();
        assertTrue(mil.isEmpty());
        assertEquals(0, mil.countDifferent());

        mil.push((0));
        assertEquals(1, mil.size());
        assertEquals(1, mil.countDifferent());

        for(int i = 0; i < 10; i++){
            mil.push((0));
            assertEquals(2 + i, mil.size());
            assertEquals(1, mil.countDifferent());
        }


    }

    @Test
    void testRepRemoval(){
        final MyIntegerList mil = generatedPopulatedList();
        assertEquals(11, mil.size());
        assertEquals("[1,2,1,6,6,7,2,2,0,5,10]", mil.toString());

        mil.removeRepetitions();

        assertEquals(7, mil.size());
        assertEquals("[1,2,6,7,0,5,10]", mil.toString());
    }
}