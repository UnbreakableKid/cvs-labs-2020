import org.junit.Test;

import static org.junit.Assert.assertEquals;

public class Lab1Tests {

    @Test
    public void test1() {
        assertEquals(0,Lab1.identity(0));
    }

    @Test
    public void test2() {
        assertEquals(1,Lab1.identity(1));
    }
}
