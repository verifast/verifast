public class SuffixArray {

    private final int[] a;
    private final int[] suffixes;
    private final int N;
    
    /*@
    
    
    
    @*/

    public SuffixArray(int[] a)
        //@ requires array_slice(a, 0, a.length, ?elems);
        //@ ensures true;
    {
        this.a = a;
        N = a.length;
        suffixes = new int[N];
        for (int i = 0; i < N; i++) suffixes[i] = i;
        sort(suffixes);
    }


    public int select(int i)
        //@ requires false;
        //@ ensures true;
    { 
        return suffixes[i]; 
    }

 
    private int lcp(int x, int y)
        //@ requires false;
        //@ ensures true;
    {
        int l = 0;
        while (x+l<N && y+l<N && a[x+l]==a[y+l]) {
            l++;
        }
        return l;
    }


    public int lcp(int i)
        //@ requires false;
        //@ ensures true;
    {
        return lcp(suffixes[i], suffixes[i-1]);
    }


    public int compare(int x, int y)
        //@ requires false;
        //@ ensures true;
    {
        if (x == y) return 0;
        int l = 0;

        while (x+l<N && y+l<N && a[x+l] == a[y+l]) {
            l++;
        }

        if (x+l == N) return -1;
        if (y+l == N) return 1;
        if (a[x+l] < a[y+l]) return -1;
        if (a[x+l] > a[y+l]) return 1;
        
        throw new RuntimeException();
    }


    public void sort(int[] data)
        //@ requires false;
        //@ ensures true;
    {
        for(int i = 0; i < data.length + 0; i++) {
            for(int j = i; j > 0 && compare(data[j - 1], data[j]) > 0; j--) {
                int b = j - 1;
                int t = data[j];
                data[j] = data[b];
                data[b] = t;
            }
        }
    }


    public static void main(String[] argv)
        //@ requires false;
        //@ ensures true;
    {
        int[] arr = {1,2,2,5};
        SuffixArray sa = new SuffixArray(arr);
        System.out.println(sa.lcp(1,2));
        int[] brr = {1,2,3,5};
        sa = new SuffixArray(brr);
        System.out.println(sa.lcp(1,2));
        int[] crr = {1,2,3,5};
        sa = new SuffixArray(crr);
        System.out.println(sa.lcp(2,3));
        int[] drr = {1,2,3,3};
        sa = new SuffixArray(drr);
        System.out.println(sa.lcp(2,3));
    }


}



//Based on code by Robert Sedgewick and Kevin Wayne.
