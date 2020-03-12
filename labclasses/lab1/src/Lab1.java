public class Lab1 {

    static int identity(int i) {
        return i;
    }

    // Return the maximum number of the first N numbers in array a
    static int max(int[] a, int n) {
        if (a == null)
            throw new RuntimeException("Null array");

        if (n > a.length)
            throw new RuntimeException("N is to big.");

        int max = a[0];
        for (int i = 1; i < n; i++) {
            if (max < a[i])
                max = a[i];
        }

        return max;
    }

    // Return the index of the last occurrence of number X in array a up to position N-1
    static int findLast(int[] a, int n, int x) {
        for (int i = n-1 ; i >= 0; i--) {
            if (a[i] == x)
                return i;
        }

        return -1;
    }
}
