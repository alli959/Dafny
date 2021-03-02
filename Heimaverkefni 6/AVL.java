// H�fundur: Snorri Agnarsson, snorri@hi.is

// Hlutir af tagi AVL eru hn�tar � AVL tr� af samb�rilegum
// hlutum.
// Tilv�sun � hlut af tagi AVL getur �v� sta�i� fyrir heilt
// AVL tr�.
// Taki� eftir �v� a� einu opinberu a�ger�irnar eru static
// a�fer�ir sem eiga a� vi�halda l�glegu �standi gagna.

class AVL<T extends Comparable<? super T>>
{
    private T value;
    private int height;
    private AVL<T> left;
    private AVL<T> right;

    //    AVL tr� er tilv�sun � hlut af �essu tagi.
    //    Til �ess a� sl�k tilv�sun teljist vera AVL
    //    tr� �arf hins vegar meira til.
    //    T�m tilv�sun (null) stendur fyrir t�mt tr�.
    //    Ef tilv�sunin er ekki t�m v�sar h�n � hlut
    //    sem stendur fyrir r�t tr�sins.
    //    Til �ess a� tr�� teljist vera AVL tr� �arf tr��
    //    a� uppfylla annars vegar tv�leitartrj�askilyr�i:
    //       �ll gildi � vinstra undirtr� eru alltaf (fyrir
    //       �ll undirtr�) <= r�targildi og �ll gildi �
    //       h�gra undirtr� eru >= r�targildi.
    //    Og hins vegar AVL skilyr�i:
    //       Tilviksbreytan height inniheldur h��
    //       heildartr�sins og mismunur h��a vinstri og
    //       h�gri undirtrj�a er � mesta lagi 1.
    //    H�� t�ms tr�s (null) er skilgreint sem 0.
    
    // Til �ess a� a�ger�irnar � AVL tr� virki �arf a�
    // sj� til �ess a� engin tv� AVL tr� sem ger�ar eru
    // breytingar � hafi sameiginlega hn�ta. Ef vi�
    // vildum losna vi� �a� skilyr�i �yrftum vi� a�
    // breyta �llum �eim a�ger�um �ar sem innihaldi
    // hn�ta er breytt og �thluta �ess � sta� n�jum
    // hn�tum � hvert skipti sem vi� viljum f�ra
    // gildi fr� einum hluta tr�sins til annars.
    // Allar sn�ningsa�ger�irnar gera sl�kt til a�
    // vi�halda AVL skilyr�inu.
    
    // Notkun: tree = new AVL(value);
    // Fyrir:  value er af tagi T.
    // Eftir:  tree v�sar � eins hn�ts AVL tr� me� gildi� value � r�tinni
    public AVL( T value )
    {
        this.value = value;
        height = 1;
    }
    
    // Notkun: T x = AVL.rootValue(tree);
    // Fyrir:  tree er AVL tr�, ekki t�mt.
    // Eftir:  x er gildi� � r�t tree.
    public static<T extends Comparable<? super T>> T rootValue( AVL<T> tree )
    {
        return tree.value;
    }

    // Notkun: AVL<T> l = AVL.left(tree);
    // Fyrir:  tree er AVL tr�, ekki t�mt.
    // Eftir:  l er vinstra undirtr� tree.
    public static<T extends Comparable<? super T>> AVL<T> left( AVL<T> tree )
    {
        return tree.left;
    }

    // Notkun: AVL<T> r = AVL.right(tree);
    // Fyrir:  tree er AVL tr�, ekki t�mt.
    // Eftir:  r er h�gra undirtr� tree.
    public static<T extends Comparable<? super T>> AVL<T> right( AVL<T> tree )
    {
        return tree.right;
    }

    // Notkun: h = AVL.height(tree);
    // Fyrir:  tree er AVL tr�, m� vera t�mt.
    // Eftir:  h er h�� AVL tr�sins tree
    public static<T extends Comparable<? super T>> int height( AVL<T> tree )
    {
        if( tree==null ) return 0;
        return tree.height;
    }
    
    // Notkun: h = AVL.height(left,right);
    // Fyrir:  left og right eru AVL tr�, mega vera t�m.
    // Eftir:  h er h�� tr�s me� vinstri hluta left og h�gri hluta right
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
    // Fyrir:  tree er AVL tr�, val er af tagi T.
    // Eftir:  f er satt ef val er til � tree
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
    // Fyrir:  org er AVL tr�, value er strengur
    // Eftir:  tree er n�ja AVL tr�� sem �t kemur �egar hn�ti me� gildinu
    //         value er b�tt � org tr��
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
    // Fyrir:  tree er ekki-t�mt AVL tr�
    // Eftir:  s er minnsta (fremsta) gildi � tree.
    public static<T extends Comparable<? super T>> T min( AVL<T> tree )
    {
        if( tree==null ) return null;
        if( tree.left==null ) return tree.value;
        return min(tree.left);
    }
    
    // Notkun: s = AVL.max(tree);
    // Fyrir:  tree er ekki-t�mt AVL tr�
    // Eftir:  s er st�rsta (aftasta) gildi � tree.
    public static<T extends Comparable<? super T>> T max( AVL<T> tree )
    {
        if( tree==null ) return null;
        if( tree.right==null ) return tree.value;
        return max(tree.right);
    }
    
    // Notkun: tree = AVL.delete(org,value);
    // Fyrir:  org er AVL tr�, value er af tagi T
    // Eftir:  tree er n�ja AVL tr�� sem �t kemur �egar hn�ti me� gildinu
    //         value er eytt � org tr�nu (ef einhver sl�kur hn�tur er til,
    //         annars er tree sama tr� og org).
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
    // Fyrir:  tree hefur r�t og vinstra barn
    // Eftir:  B�i� er a� sn�a tr� og uppf�ra h��ir mi�a�
    //         vi� eftirfarandi mynd og skila tilv�sun �
    //         n�ju r�tina.
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
    // Fyrir:  tree hefur r�t og h�gra barn
    // Eftir:  B�i� er a� sn�a tr� og uppf�ra h��ir mi�a�
    //         vi� eftirfarandi mynd og skila tilv�sun �
    //         n�ju r�tina.
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
    // Fyrir:  tree hefur r�t og vinstra barn og vinstra
    //         barn hefur h�gra barn.
    // Eftir:  B�i� er a� sn�a tr� og uppf�ra h��ir mi�a�
    //         vi� eftirfarandi mynd og skila tilv�sun �
    //         n�ju r�tina.
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
    // Fyrir:  tree hefur r�t og h�gra barn og h�gra
    //         barn hefur vinstra barn.
    // Eftir:  B�i� er a� sn�a tr� og uppf�ra h��ir mi�a�
    //         vi� eftirfarandi mynd og skila tilv�sun �
    //         n�ju r�tina.
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
