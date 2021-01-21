public class Binarysearchdec {

    
    // Notkun: int k = searchRecursive(a,i,j,x);
    // Fyrir:  a[i..j-1] er svæði í a, í minnkandi röð.
    // Eftir:  i <= k <= j,
    //         öll gildi í a[i..k-1] eru >=x,
    //         öll gildi í a[k..j-1] eru <x.
    public static int searchRecursive( int[] a, int i, int j, int x )
    {
        if( i == j ) {

            return i;
        } 
        int m = i + (j-i)/2;
        if( a[m] >= x ) {

            return searchRecursive(a,i,m-1,x);
        }
        else {
            
            return searchRecursive(a,m+1,j,x);
        }
    }
/*
    // Notkun: int k = searchLoop(a,i,j,x);
    // Fyrir:  a[i..j-1] er svæði í a, í minnkandi röð.
    // Eftir:  i <= k <= j,
    //         öll gildi í a[i..k-1] eru >=x,
    //         öll gildi í a[k..j-1] eru <x.
    static int searchLoop( double[] a, int i, int j, double x )
    {
        int p = ?F?;
        int q = ?G?;
        while( ?H? )
        // Loop invariant:
            //    ?I?
            {
                int m = ?J?;
            if( a[m] ?K? x )
            p = ?L?;
            else
            q = ?M?;
        }
        return ?N?;
    }*/
    public static void main(String[] args){
        int[] a = {9,8,7,6,5,4,3,2,1};
        System.out.println(searchRecursive(a,0,a.length-1,0));
        
    }
}