// Höfundur: Snorri Agnarsson, snorri@hi.is

// Hlutir af tagi AVL eru hnútar í AVL tré af sambærilegum
// hlutum.
// Tilvísun í hlut af tagi AVL getur því staðið fyrir heilt
// AVL tré.
// Takið eftir því að einu opinberu aðgerðirnar eru static
// aðferðir sem eiga að viðhalda löglegu ástandi gagna.

class AVL<T extends Comparable<? super T>>
{
    private T value;
    private int height;
    private AVL<T> left;
    private AVL<T> right;

    //    AVL tré er tilvísun á hlut af þessu tagi.
    //    Til þess að slík tilvísun teljist vera AVL
    //    tré þarf hins vegar meira til.
    //    Tóm tilvísun (null) stendur fyrir tómt tré.
    //    Ef tilvísunin er ekki tóm vísar hún á hlut
    //    sem stendur fyrir rót trésins.
    //    Til þess að tréð teljist vera AVL tré þarf tréð
    //    að uppfylla annars vegar tvíleitartrjáaskilyrði:
    //       Öll gildi í vinstra undirtré eru alltaf (fyrir
    //       öll undirtré) <= rótargildi og öll gildi í
    //       hægra undirtré eru >= rótargildi.
    //    Og hins vegar AVL skilyrði:
    //       Tilviksbreytan height inniheldur hæð
    //       heildartrésins og mismunur hæða vinstri og
    //       hægri undirtrjáa er í mesta lagi 1.
    //    Hæð tóms trés (null) er skilgreint sem 0.
    
    // Til þess að aðgerðirnar á AVL tré virki þarf að
    // sjá til þess að engin tvö AVL tré sem gerðar eru
    // breytingar á hafi sameiginlega hnúta. Ef við
    // vildum losna við það skilyrði þyrftum við að
    // breyta öllum þeim aðgerðum þar sem innihaldi
    // hnúta er breytt og úthluta þess í stað nýjum
    // hnútum í hvert skipti sem við viljum færa
    // gildi frá einum hluta trésins til annars.
    // Allar snúningsaðgerðirnar gera slíkt til að
    // viðhalda AVL skilyrðinu.
    
    // Notkun: tree = new AVL(value);
    // Fyrir:  value er af tagi T.
    // Eftir:  tree vísar á eins hnúts AVL tré með gildið value í rótinni
    public AVL( T value )
    {
        this.value = value;
        height = 1;
    }
    
    // Notkun: T x = AVL.rootValue(tree);
    // Fyrir:  tree er AVL tré, ekki tómt.
    // Eftir:  x er gildið í rót tree.
    public static<T extends Comparable<? super T>> T rootValue( AVL<T> tree )
    {
        return tree.value;
    }

    // Notkun: AVL<T> l = AVL.left(tree);
    // Fyrir:  tree er AVL tré, ekki tómt.
    // Eftir:  l er vinstra undirtré tree.
    public static<T extends Comparable<? super T>> AVL<T> left( AVL<T> tree )
    {
        return tree.left;
    }

    // Notkun: AVL<T> r = AVL.right(tree);
    // Fyrir:  tree er AVL tré, ekki tómt.
    // Eftir:  r er hægra undirtré tree.
    public static<T extends Comparable<? super T>> AVL<T> right( AVL<T> tree )
    {
        return tree.right;
    }

    // Notkun: h = AVL.height(tree);
    // Fyrir:  tree er AVL tré, má vera tómt.
    // Eftir:  h er hæð AVL trésins tree
    public static<T extends Comparable<? super T>> int height( AVL<T> tree )
    {
        if( tree==null ) return 0;
        return tree.height;
    }
    
    // Notkun: h = AVL.height(left,right);
    // Fyrir:  left og right eru AVL tré, mega vera tóm.
    // Eftir:  h er hæð trés með vinstri hluta left og hægri hluta right
    public static<T extends Comparable<? super T>> int height( AVL<T> left, AVL<T> right )
    {
        int leftheight = height(left);
        int rightheight = height(right);
        if( leftheight > rightheight )
            return leftheight+1;
        else
            return rightheight+1;
    }
    
    // Notkun: f = AVL.find(tree,val);
    // Fyrir:  tree er AVL tré, val er af tagi T.
    // Eftir:  f er satt ef val er til í tree
    public static<T extends Comparable<? super T>> boolean find( AVL<T> tree, T val )
    {
        if( tree==null )
            return false;
        if( tree.value.equals(val) )
            return true;
        if( val.compareTo(tree.value) < 0 )
            return find(tree.left,val);
        else
            return find(tree.right,val);
    }
    
    // Notkun: tree = AVL.insert(org,value);
    // Fyrir:  org er AVL tré, value er strengur
    // Eftir:  tree er nýja AVL tréð sem út kemur þegar hnúti með gildinu
    //         value er bætt í org tréð
    public static<T extends Comparable<? super T>> AVL<T> insert( AVL<T> org, T value )
    {
        if( org==null )
            return new AVL<T>(value);
        if( value.compareTo(org.value) < 0 )
        {
            org.left = insert(org.left,value);
            org.height = height(org.left,org.right);
            if( org.left.height > height(org.right)+1 )
                if( height(org.left.left) >= height(org.left.right) )
                    org = rotateLeftUp(org);
                else
                    org = rotateLeftRightUp(org);
        }
        else
        {
            org.right = insert(org.right,value);
            org.height = height(org.left,org.right);
            if( org.right.height > height(org.left)+1 )
                if( height(org.right.right) >= height(org.right.left) )
                    org = rotateRightUp(org);
                else
                    org = rotateRightLeftUp(org);
        }
        return org;
    }
    
    // Notkun: s = AVL.min(tree);
    // Fyrir:  tree er ekki-tómt AVL tré
    // Eftir:  s er minnsta (fremsta) gildi í tree.
    public static<T extends Comparable<? super T>> T min( AVL<T> tree )
    {
        if( tree==null ) return null;
        if( tree.left==null ) return tree.value;
        return min(tree.left);
    }
    
    // Notkun: s = AVL.max(tree);
    // Fyrir:  tree er ekki-tómt AVL tré
    // Eftir:  s er stærsta (aftasta) gildi í tree.
    public static<T extends Comparable<? super T>> T max( AVL<T> tree )
    {
        if( tree==null ) return null;
        if( tree.right==null ) return tree.value;
        return max(tree.right);
    }
    
    // Notkun: tree = AVL.delete(org,value);
    // Fyrir:  org er AVL tré, value er af tagi T
    // Eftir:  tree er nýja AVL tréð sem út kemur þegar hnúti með gildinu
    //         value er eytt í org trénu (ef einhver slíkur hnútur er til,
    //         annars er tree sama tré og org).
    public static<T extends Comparable<? super T>> AVL<T> delete( AVL<T> org, T val )
    {
        if( org==null ) return null;
        if( val.equals(org.value) )
        {
            if( height(org.left) > height(org.right) )
            {
                org.value = max(org.left);
                org.left = delete(org.left,org.value);
                org.height = height(org.left,org.right);
                return org;
            }
            else if( org.right != null )
            {
                org.value = min(org.right);
                org.right = delete(org.right,org.value);
                org.height = height(org.left,org.right);
                return org;
            }
            else
                return null;
        }
        if( val.compareTo(org.value) < 0 )
        {
            org.left = delete(org.left,val);
            org.height = height(org.left,org.right);
            if( height(org.left) == height(org.right)-2 )
                if( height(org.right.left) > height(org.right.right) )
                    org = rotateRightLeftUp(org);
                else
                    org = rotateRightUp(org);
        }
        else
        {
            org.right = delete(org.right,val);
            org.height = height(org.left,org.right);
            if( height(org.right) == height(org.left)-2 )
                if( height(org.left.right) > height(org.left.left) )
                    org = rotateLeftRightUp(org);
                else
                    org = rotateLeftUp(org);
        }
        return org;
    }
    
    // Notkun: tree = rotateLeftUp(tree);
    // Fyrir:  tree hefur rót og vinstra barn
    // Eftir:  Búið er að snúa tré og uppfæra hæðir miðað
    //         við eftirfarandi mynd og skila tilvísun á
    //         nýju rótina.
    //                     x            y
    //                    / \          / \
    //                   y   C  =>    A   x
    //                  / \              / \
    //                 A   B            B   C
    private static<T extends Comparable<? super T>> AVL<T> rotateLeftUp( AVL<T> tree )
    {
        AVL<T> x=tree, y=x.left, A=y.left, B=y.right, C=x.right;
        x.left = B; x.right = C; x.height = height(B,C);
        y.left = A; y.right = x; y.height = height(A,x);
        return y;
    }
    
    // Notkun: tree = rotateRightUp(tree);
    // Fyrir:  tree hefur rót og hægra barn
    // Eftir:  Búið er að snúa tré og uppfæra hæðir miðað
    //         við eftirfarandi mynd og skila tilvísun á
    //         nýju rótina.
    //                  x              y
    //                 / \            / \
    //                A   y   =>     x   C
    //                   / \        / \
    //                  B   C      A   B
    private static<T extends Comparable<? super T>> AVL<T> rotateRightUp( AVL<T> tree )
    {
        AVL<T> x=tree, y=x.right, A=x.left, B=y.left, C=y.right;
        x.left = A; x.right = B; x.height = height(A,B);
        y.left = x; y.right = C; y.height = height(x,C);
        return y;
    }
    
    // Notkun: tree = rotateLeftRightUp(tree);
    // Fyrir:  tree hefur rót og vinstra barn og vinstra
    //         barn hefur hægra barn.
    // Eftir:  Búið er að snúa tré og uppfæra hæðir miðað
    //         við eftirfarandi mynd og skila tilvísun á
    //         nýju rótina.
    //                     x            z
    //                    / \          / \
    //                   y   D  =>    /   \
    //                  / \          y     x
    //                 A   z        / \   / \
    //                    / \      A   B C   D
    //                   B   C
    private static<T extends Comparable<? super T>> AVL<T> rotateLeftRightUp( AVL<T> tree )
    {
        AVL<T> x=tree, y=x.left, z=y.right, A=y.left, B=z.left, C=z.right, D=x.right;
        x.left = C; x.right = D; x.height = height(C,D);
        y.left = A; y.right = B; y.height = height(A,B);
        z.left = y; z.right = x; z.height = height(x,y);
        return z;
    }

    // Notkun: tree = rotateRightLeftUp(tree);
    // Fyrir:  tree hefur rót og hægra barn og hægra
    //         barn hefur vinstra barn.
    // Eftir:  Búið er að snúa tré og uppfæra hæðir miðað
    //         við eftirfarandi mynd og skila tilvísun á
    //         nýju rótina.
    //                     x              z
    //                    / \            / \
    //                   A   y    =>    /   \
    //                      / \        x     y
    //                     z   D      / \   / \
    //                    / \        A   B C   D
    //                   B   C
    private static<T extends Comparable<? super T>> AVL<T> rotateRightLeftUp( AVL<T> tree )
    {
        AVL<T> x=tree, y=x.right, z=y.left, A=x.left, B=z.left, C=z.right, D=y.right;
        x.left = A; x.right = B; x.height = height(A,B);
        y.left = C; y.right = D; y.height = height(C,D);
        z.left = x; z.right = y; z.height = height(x,y);
        return z;
    }
}
