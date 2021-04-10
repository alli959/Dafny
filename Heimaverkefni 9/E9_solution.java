// Höfundur: Snorri Agnarsson, snorri@hi.is

// Listar án hliðarverkana í Java.

public class E9
{
    // Tilvik af link eru óbreytanlegir hlekkir með
    // haus sem er heiltala og hala sem er endanleg
    // keðja hlekkja.  Takið eftir að það er enginn
    // möguleiki á að breyta halanum og því eru allar
    // keðjur endanlegar.  Tóm keðja er táknuð með null.
    public static class Link
    {
        private int head;
        private Link tail;
        
        // Notkun: E9.Link x = new E9.Link(head,tail);
        // Fyrir:  head er heiltala, tail er E9.Link (má vera null).
        // Eftir:  x er tilvísun á nýjan E9.Link með gefinn haus og
        //         og hala.
        public Link( int head, Link tail )
        {
            this.head = head;
            this.tail = tail;
        }
        
        // Notkun: int h = link.head();
        // Fyrir:  link vísar á E9.Link.
        // Eftir:  h er hausinn á link.
        public int head()
        {
            return head;
        }
        
        // Notkun: E9.Link t = link.tail();
        // Fyrir:  link vísar á E9.Link.
        // Eftir:  t er halinn á link.
        public Link tail()
        {
            return tail;
        }
    }
    
    // Notkun: E9.Link x = E9.cons(head,tail);
    // Fyrir:  head er heiltala, tail er E9.Link (má vera null).
    // Eftir:  x er tilvísun á nýjan E9.Link með gefinn haus og
    //         og hala.
    public static Link cons( int h, Link t )
    {
        return new Link(h,t);
    }
    
    // Notkun: int h = head(x);
    // Fyrir:  x er tilvísun á E9.Link, má ekki vera null.
    // Eftir:  h er hausinn á x.
    public static int head( Link x )
    {
        return x.head();
    }
    
    // Notkun: E9.Link t = tail(x);
    // Fyrir:  x er tilvísun á E9.Link, má ekki vera null.
    // Eftir:  h er halinn á x.
    public static Link tail( Link x )
    {
        return x.tail();
    }
        
    // Notkun: int n = E9.length(x);
    // Fyrir:  x er E9.Link tilvísun, má vera null.
    // Eftir:  n er fjöldi hlekkja í keðju x.
    public static int length( E9.Link x )
    {
        int n = 0;
        Link z = x;
        while( z != null )
            // z er aftari hluti keðjunnar x.
            // Hlekkirnir í x sem ekki eru í z
            // eru n talsins.
        {
            n++;
            z = tail(z);
        }
        return n;
    }

    // Notkun: int i = E9.nth(x,n);
    // Fyrir:  x er keðja með a.m.k. n+1 hlekki.
    // Eftir:  i er hausinn á n-ta hlekk í keðjunni
    //         þar sem 0-ti hlekkur er fremsti hlekkur.
    public static int nth( E9.Link x, int n )
    {
        int i = 0;
        Link z = x;
        while( i != n )
            // z er aftari hluti keðjunnar x.
            // Hlekkirnir í x sem ekki eru í z
            // eru i talsins.
        {
            i++;
            z = tail(z);
        }
        return head(z);
    }
    
    // Notkun: E9.Link x = makeChain(a);
    // Fyrir:  a er tilvísun á int[]. Má ekki vera null
    //         en má vera tómt.
    // Eftir:  x er keðja nýrra hlekkja sem inniheldur gildin í a
    //         þannig að fyrir i=0,...,a.length gildir
    //         E9.nth(x,i) == a[i].
    public static Link makeChain( int[] a )
    {
        int i = a.length;
        Link z = null;
        while( i != 0 )
            // z er keðja nýrra hlekkja sem inniheldur a[i..a.length),
            // í þeirri röð.
            // 0 <= i <= a.length.
        {
            i--;
            z = cons(a[i],z);
        }
        return z;
    }
    
    // Notkun: int i = E9.last(x);
    // Fyrir:  x er tilvísun á E9.Link, má ekki vera null.
    // Eftir:  i er gildið í (hausinn á) aftasta hlekk x.
    public static int last( Link x )
    {
        Link z = x;
        while( tail(z) != null )
            // z er aftari hluti keðju x.
            // z er ekki null.
        {
            z = tail(z);
        }
        return head(z);
    }

    // Notkun: E9.Link z = E9.removeLast(x);
    // Fyrir:  x er tilvísun á E9.Link, má ekki vera null.
    // Eftir:  z er keðja sem inniheldur nýja hlekki
    //         þannig að E9.length(z) == E9.length(x)-1
    //         og fyrir i=0,...,E9.length(z)-1 gildir
    //         E9.nth(z,i) == E9.nth(z,i).
    public static Link removeLast( Link x )
    {
        Link z = null;
        Link w = x;
        while( tail(w) != null )
            // w er aftari hluti keðjunnar x, ekki tómur.
            // z er keðja nýrra hlekkja sem inniheldur sömu gildin
            // og þeir hlekkir x sem ekki eru í w, í öfugri röð
            // miðað við röðina í x.
        {
            z = cons(head(w),z);
            w = tail(w);
        }
        return reverse(z);
        
        /*
        // Einnig má skrifa útgáfu með einni lykku án kalls á
        // reverse sem hefur tímaflækju O(n^2):
        Link z = null;
        int i = 0, n = E9.length(x);
        while( i != n-1 )
            // n er fjöldi hlekkja í x.
            // 0 <= i <= n-1.
            // z er keðja nýrra hlekkja af lengd i sem inniheldur
            // sömu gildi í sömu röð og næstöftustu hlekkirnir
            // í x. Með öðrum orðum gildir fyrir j þ.a. 0 <= j < i
            // að E9.nth(w,j) == E9.nth(x,n-j-i-1).
            // Ef við notum svipaðan rithátt fyrir svæði í keðju og
            // nota má í Dafny þá getum við skrifað
            //        0 <= i <= n-1
            //        |ListSeq(z)| == i
            //        |ListSeq(x)| == n
            //        ListSeq(z) == ListSeq(x)[n-i-1..n-1)
        {
            i = i+1;
            z = E9.cons(E9.nth(x,n-i-1),z);
        }
        return z;
        */
        
        /*
        // Ef ekki hefði verið krafa um að ekki mætti nota
        // endurkvæmni, gætum við skrifað lausnina svona:
        if( E9.tail(x) == null ) { return null; }
        return E9.cons(E9.head(x),E9.removeLast(E9.tail(x)));
        */
    }
    
    // Notkun: E9.Link r = E9.reverse(x);
    // Fyrir:  x er keðja, má vera tóm.
    // Eftir:  z er jafn löng keðja og x, þannig að
    //         fyrir i=0,...,E9.length(x)-1 gildir
    //         E9.nth(x,i) == E9.nth(r,E9.length(x)-i-1).
    public static Link reverse( Link x )
    {
        Link res = null;
        Link z = x;
        while( z != null )
            // z er aftari hluti keðjunnar x.
            // res er keðja nýrra hlekkja sem inniheldur
            // sömu gildi og þeir hlekkir x sem ekki eru
            // í z, en í öfugri röð.
        {
            res = cons(head(z),res);
            z = tail(z);
        }
        return res;
    }
   
    public static void main( String[] args )
    {
        E9.Link x = null;
        for( int i=0 ; i!=args.length ; i++ )
            x = E9.cons(Integer.parseInt(args[i]),x);
        while( x != null )
        {
            E9.Link z = reverse(x);
            x = z;
            while( z != null )
            {
                System.out.print(z.head); System.out.print(" ");
                z = z.tail;
            }
            x = E9.removeLast(x);
            System.out.println();
        }
    }
}