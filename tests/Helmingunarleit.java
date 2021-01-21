public class Helmingunarleit
{
    // Notkun: k = searchRec(a,i,j,x);
    // Fyrir:  a[i..j-1] er í vaxandi röð.
    //
    //          a: | ... | í vaxandi röð | ... |
    //                    i               j
    //
    // Eftir:  i <= k <= j,
    //         a[i..k-1] < x <= a[k..j-1].
    //
    //          a: | ... | í vaxandi röð | ... |
    //             |     | <x |   >=x    |     |
    //                    i    k          j
    //
    public static int searchRec( int[] a, int i, int j, int x )
    {
        if( i == j ) return i;
        int m = i+(j-i)/2;
        //
        // a: | ... |   í vaxandi röð  | ... |
        //    |     |       |?|        |     |
        //           i       m          j
        //
        if( a[m] < x ) return searchRec(a,m+1,j,x);
        else           return searchRec(a,i,m,x);
    }

    // Notkun: k = searchLoop(a,i,j,x);
    // Fyrir:  a[i..j-1] er í vaxandi röð.
    //
    //          a: | ... | í vaxandi röð | ... |
    //                    i               j
    // Eftir:  i <= k <= j,
    //         a[i..k-1] < x <= a[k..j-1].
    //
    //          a: | ... | í vaxandi röð | ... |
    //             |     | <x |   >=x    |     |
    //                    i    k          j
    //
    public static int searchLoop( int[] a, int i, int j, int x )
    {
        int p=i, q=j;
        while( p != q )
        // a: | ... | í vaxandi röð  | ... |
        //    |     | <x | ??? | >=x |     |
        //           i    p     q     j
        {
            int m = p+(q-p)/2;
            //
            // a: | ... |   í vaxandi röð  | ... |
            //    |     | <x |  |?|  | >=x |     |
            //           i    p  m    q     j
            //
            if( a[m] < x ) p = m+1;
            else           q = m;
        }
        return p;
    }

    public static void main(String[] args){

        int[] a = {0,1,2,3,4,5,6,7,8,9}; 
        int i = 0;
        int j = a.length;
        int rec = searchRec(a,i,j,5);
        int loop = searchLoop(a,i,j,5);

        System.out.println(rec);
        System.out.println(loop);



    }
}
