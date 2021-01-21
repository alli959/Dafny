public class Binarysearchdec {

    
    // Notkun: int k = searchRecursive(a,i,j,x);
    // Fyrir:  a[i..j-1] er svæði í a, í minnkandi röð.
    // Eftir:  i <= k <= j,
    //         öll gildi í a[i..k-1] eru >=x,
    //         öll gildi í a[k..j-1] eru <x.
    public static int searchRecursive( double[] a, int i, int j, double x )
    {
        if( i == j ) {

            return i;
        } 
        int m = i + (j-i)/2;
        if( a[m] <= x ) {

            return searchRecursive(a,i,m,x);
        }
        else {
            
            return searchRecursive(a,m+1,j,x);
        }
    }

    // Notkun: int k = searchLoop(a,i,j,x);
    // Fyrir:  a[i..j-1] er svæði í a, í minnkandi röð.
    // Eftir:  i <= k <= j,
    //         öll gildi í a[i..k-1] eru >=x,
    //         öll gildi í a[k..j-1] eru <x.
    static int searchLoop( double[] a, int i, int j, double x )
    {
        int p = i;
        int q = j;
        while( p != q )
        // Loop invariant:
            //    ?I?
            {
                int m = i + ( j-i )/2;
                if( a[m] > x )
                p = m+1;
                else
                q = m-1;
            }
        return p;
    }


    public static void main(String[] args){
        double[] a = {9,8,4,3,2,1,-1,-14};
        System.out.println(searchRecursive(a,0,a.length,9));
        System.out.println(searchLoop(a,0,a.length,9));
        System.out.println(searchRecursive(a,0,a.length,8));
        System.out.println(searchLoop(a,0,a.length,8));
        System.out.println(searchRecursive(a,0,a.length,5));
        System.out.println(searchLoop(a,0,a.length,5));
        System.out.println(searchRecursive(a,0,a.length,4));
        System.out.println(searchLoop(a,0,a.length,4));
        System.out.println(searchRecursive(a,0,a.length,3));
        System.out.println(searchLoop(a,0,a.length,3));
        System.out.println(searchRecursive(a,0,a.length,2));
        System.out.println(searchLoop(a,0,a.length,2));
        System.out.println(searchRecursive(a,0,a.length,1));
        System.out.println(searchLoop(a,0,a.length,1));
        System.out.println(searchRecursive(a,0,a.length,-1));
        System.out.println(searchLoop(a,0,a.length,-14));
    }
}