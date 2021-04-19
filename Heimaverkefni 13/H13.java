public class H13
{
    // Notkun: t2 = insert(t1,x);
    // Fyrir:  t1 er tv�leitartr�, x er heiltala
    // Eftir:  t2 er tv�leitartr� sem inniheldur
    //         �ll heilt�lugildin � t1 �samt x.
    public static BSTNode insert( BSTNode t, int x )
    {
        if (t == null)
        {
            t = new BSTNode(null,x,null);
            return t;
        }
        BSTNode left = BSTNode.left(t);
        BSTNode right = BSTNode.right(t);
        int val = BSTNode.rootValue(t);
        /* If the tree is empty,
        return a new node */

        /* Otherwise, recur down the tree */
        if (x > val) {
            left = insert(left,x);
            t = new BSTNode(left,x,right);  
        }
        else if (x < val) {
            right = insert(right,x);
            t = new BSTNode(left,x,right);  
        }

        /* return the (unchanged) node pointer */
        return t;
    }

    // Notkun: t2 = delete(t1,x);
    // Fyrir:  t1 er tv�leitartr�, x er heiltala
    // Eftir:  t2 er tv�leitartr� sem inniheldur
    //         �ll heilt�lugildin � t1 nema hva�
    //         eitt x hefur veri� fjarl�gt ef �a�
    //         var til sta�ar.
   public static BSTNode delete( BSTNode t, int x )
    {
        /* Base Case: If the tree is empty */
        if (t == null) {
            return t;
        }

        BSTNode left = BSTNode.left(t);
        BSTNode right = BSTNode.right(t);
        int val = BSTNode.rootValue(t);
 
        /* Otherwise, recur down the tree */
        if (x > val){

            left = delete(left, x);
            t = new BSTNode(left,val,right);
        }
        else if (x < val) {
            right = delete(right, x);
            t = new BSTNode(left,val,right);
        }
 
        // if key is same as root's
        // key, then This is the
        // node to be deleted
        else {
            if(x == val) {
                
            }
            // node with only one child or no child
            if (left == null)
                return right;
            else if (right == null)
                return left;
 
            // node with two children: Get the inorder
            // successor (smallest in the right subtree)
 
            // Delete the inorder successor
            left = delete(left, x);
            t = left;
        }
 
        return t;
    }

    // Notkun: x = max(t);
    // Fyrir:  t er tv�leitartr�, ekki t�mt.
    // Eftir:  x er st�rsta gildi� � t.
    public static int max( BSTNode t )
    {
        // Muni� a� ef �i� noti� lykkju h�r ��
        // �arf h�n fastayr�ingu.
        BSTNode left = BSTNode.left(t);
        int val = BSTNode.rootValue(t);
        if(left == null) {
            return val;
        }
        else {
            return max(left);
        }

        


    }

    // Notkun: java H13 i1 i2 ... iN
    // Fyrir:   i1, i2, ..., iN eru heiltölur
    // Eftir:   Búið er að skrifa tölurnar í
    //          minnkandi röð á aðalúttak.
    public static void main( String[] args) 
    {
        BSTNode t = null;
        for( int i=0; i!=args.length; i++) 
            // t er tvíleitartré sem inniheldur
            // tölurnar úr args[0..i).
        {
            t = insert(t,Integer.parseInt(args[i]));
        }
        while( t != null )
            // búið er að skrifa núll eða fleiri
            // stærstu tölurnar í minnkandi röð.
            // t er tvíleitartré sem inniheldur
            // afganginn af tölunum.
        {
            int m = max(t);
            System.out.print(m + " ");
            t = delete(t,m);
        }
    }
}