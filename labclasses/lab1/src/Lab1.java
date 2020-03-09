public class Lab1 {

    static int identity(int i) {
        return i;
    }

    // Return the maximum number of the first N numbers in array a
    static int max(int[] a, int N) {
        int max = Integer.MIN_VALUE;
        for (int i = 0; i < N ; i++) {
            if(a[i] > max)
                max = a[i];
        }
        return max;
    }

    // Return the index of the last occurrence of number X in array a up to position N-1
    static int findLast(int[] a, int N, int X) {
        int sol = -1;
        for (int i = 0; i < N ; i++) {
            if(a[i] == X)
                sol = i;
        }
       return sol;
    }
}
