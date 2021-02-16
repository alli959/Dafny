// Dæmigerðar trjáleitaraðferðir í Java.
// Höfundur: Snorri Agnarsson, snorri@hi.is

class AVLSearch
{
    // Notkun: AVL<T> r = searchAnyEQ_Loop(t,x);
    // Fyrir:  t er AVL<T> í vaxandi röð, x er af tagi T,
    //         x er ekki null.
    // Eftir:  r vísar á hnút í t sem hefur gildi x,
    //         ef slíkur hnútur er til í t. Annars er
    //         r jafnt null.
    public static<T extends Comparable<? super T>> AVL<T> searchAnyEQ_Loop( AVL<T> t, T x )
    {
        AVL<T> s = t;
        // ghost ps = [];
        while( s != null )
            // s == Subtree(t,ps).
            // Allt í PreSeq(t,ps) er <x.
            // Allt í PostSeq(t,ps) er >x.
        {
            T z = AVL.rootValue(s);
            if( x.compareTo(z) == 0 ) return s;
            if( x.compareTo(z) < 0 )
                s = AVL.left(s);
                // ps = ps+[0];
            else
                s = AVL.right(s);
                // ps = ps+[1];
        }
        return null;
    }
    
    // Notkun: AVL<T> r = searchAnyEQ_Recursive(t,x);
    // Fyrir:  t er AVL<T> í vaxandi röð, x er af tagi T,
    //         x er ekki null.
    // Eftir:  r vísar á hnút í t sem hefur gildi x,
    //         ef slíkur hnútur er til í t. Annars er
    //         r jafnt null.
    public static<T extends Comparable<? super T>> AVL<T> searchAnyEQ_Recursive( AVL<T> t, T x )
    {
        if( t == null ) return null;
        if( AVL.rootValue(t).compareTo(x) == 0 ) return t;
        if( AVL.rootValue(t).compareTo(x) < 0 )
            return searchAnyEQ_Recursive(AVL.right(t),x);
        else
            return searchAnyEQ_Recursive(AVL.left(t),x);
    }

    // Notkun: AVL<T> r = searchFirstGE_Recursive(t,x);
    // Fyrir:  t er AVL<T> í vaxandi röð, x er af tagi T,
    //         x er ekki null.
    // Eftir:  r vísar á fremsta hnút t sem hefur gildi
    //         >=x, ef slíkur hnútur er til í t. Annars er
    //         r jafnt null.
    public static<T extends Comparable<? super T>> AVL<T> searchFirstGE_Recursive( AVL<T> t, T x )
    {
        if( t == null ) return null;
        if( AVL.rootValue(t).compareTo(x) < 0 )
            return searchFirstGE_Recursive(AVL.right(t),x);
        AVL<T> r = searchFirstGE_Recursive(AVL.left(t),x);
        if( r == null ) return t;
        return r;
    }

    // Notkun: AVL<T> r = searchFirstGE_TailRecursive(t,x,c);
    // Fyrir:  t er AVL<T> í vaxandi röð, x er af tagi T,
    //         x er ekki null, c er AVL<T> eða null.
    // Eftir:  r vísar á fremsta hnút t sem hefur gildi
    //         >=x, ef slíkur hnútur er til í t. Annars er
    //         r jafnt c.
    public static<T extends Comparable<? super T>> AVL<T> searchFirstGE_TailRecursive( AVL<T> t, T x, AVL<T> c )
    {
        if( t == null ) return c;
        if( AVL.rootValue(t).compareTo(x) < 0 )
            return searchFirstGE_TailRecursive(AVL.right(t),x,c);
        else
            return searchFirstGE_TailRecursive(AVL.left(t),x,t);
    }

    // Notkun: AVL<T> r = searchFirstGE_Loop(t,x);
    // Fyrir:  t er AVL<T> í vaxandi röð, x er af tagi T,
    //         x er ekki null.
    // Eftir:  r vísar á fremsta hnút t sem hefur gildi
    //         >=x, ef slíkur hnútur er til í t. Annars er
    //         r jafnt null.
    public static<T extends Comparable<? super T>> AVL<T> searchFirstGE_Loop( AVL<T> t, T x )
    {
        AVL<T> s = t;
        // ghost sp = [];
        AVL<T> r = null;
        // ghost rp = [];
        while( s != null )
            // s == Subtree(t,sp).
            // Allt í PreSeq(t,sp) er <x.
            // Allt í PostSeq(t,sp) er >=x.
            // Ef r er null þá er PostSeq(t,sp) tómt.
            // Ef r er ekki null þá er PostSeq(t,sp)
            // ekki tómt og r==Subtree(t,rp) og
            // PostSeq(t,sp)==PostSeqIncluding(t,rp).
        {
            T z = AVL.rootValue(s);
            if( z.compareTo(x) < 0 )
                s = AVL.right(s);
                // sp = sp+[0];
            else
            {
                r = s;
                // rp = sp;
                s = AVL.left(s);
                // sp = sp+[1];
            }
        }
        return r;
    }
    
    private static void testAnyEQ( java.util.function.Function<Integer,AVL<Integer>> f, AVL<Integer> t )
    {
        for( int i=0 ; i!=1000000 ; i++ )
        {
            int x = (int)(java.lang.Math.random()*3000.0)-500;
            AVL<Integer> s = f.apply(x);
            if( s != null )
            {
                if( AVL.rootValue(s) != x ) throw new Error();
                if( !AVL.find(t,x) ) throw new Error();
            }
            else
            {
                if( x%2==0 && 0 <= x && x < 2000 ) throw new Error();
                if( AVL.find(t,x) ) throw new Error();
            }
        }
    }
    
    private static void testFirstGE( java.util.function.Function<Integer,AVL<Integer>> f, AVL<Integer> t )
    {
        for( int i=0 ; i!=1000000 ; i++ )
        {
            int x = (int)(java.lang.Math.random()*3000.0)-500;
            AVL<Integer> s = f.apply(x);
            if( s != null )
            {
                if( AVL.rootValue(s) < x )
                    throw new Error(""+x);
                if( x <= 0 && AVL.rootValue(s) != 0 )
                    throw new Error(""+x);
                if( x >= 0 && (x+1)/2*2 != AVL.rootValue(s) )
                    throw new Error(""+x);
                if( AVL.left(s) != null && AVL.rootValue(AVL.left(s)) >= x )
                    throw new Error(""+x);
            }
            else
            {
                if( x <= 1998 ) throw new Error(""+x);
                if( AVL.find(t,x) ) throw new Error();
            }
        }
    }
    
    public static void main( String[] args )
    {
        AVL<Integer> t = null;
        for( int n=0 ; n!=100 ; n++ )
            for( int i=0 ; i!=1000 ; i++ )
                t = AVL.insert(t,2*i);
        final AVL<Integer> s = t;
        testAnyEQ( i -> searchAnyEQ_Loop(s,i), s );
        testAnyEQ( i -> searchAnyEQ_Recursive(s,i), s );
        testFirstGE( i -> searchFirstGE_Recursive(s,i), s );
        testFirstGE( i -> searchFirstGE_TailRecursive(s,i,null), s );
        testFirstGE( i -> searchFirstGE_Loop(s,i), s );
    }
}