import org.junit.Test;

import static org.junit.Assert.assertEquals;

public class Lab1Tests {

    @Test
    public void testId1() {
        assertEquals(0,Lab1.identity(0));
    }

    @Test
    public void testId2() {
        assertEquals(1,Lab1.identity(1));
    }

    @Test
    public void testMax1() {
        assertEquals(1, Lab1.max(new int[]{1,2,3,4,5,6},1));
        assertEquals(2, Lab1.max(new int[]{1,2,3,4,5,6},2));
        assertEquals(4, Lab1.max(new int[]{1,2,3,4,5,6},4));
        assertEquals(6, Lab1.max(new int[]{1,2,3,4,5,6},6));
    }

    @Test
    public void testMax2() {
        assertEquals(-1, Lab1.max(new int[]{-1,-2,-3,-4,-5,-6},1));
        assertEquals(-1, Lab1.max(new int[]{-2,-1,-3,-4,-5,-6},2));
        assertEquals(-1, Lab1.max(new int[]{-2,-3,-1,-4,-5,-6},4));
        assertEquals(-1, Lab1.max(new int[]{-4,-2,-3,-1,-5,-6},6));
    }

}
