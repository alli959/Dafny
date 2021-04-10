// Klasinn E11 notar klasann Link sem er � Link.java.
// Lesi� skilgreiningarnar og setningarnar �ar.

public class E11
{    
    // Notkun: splice(x,i,y);
    // Fyrir:  x er l�gleg ke�ja me� N hlekki og hlekkjarunu
    //           [x_0,...,x_{N-1}].
    //         0 <= i < N.
    //         y er l�gleg ke�ja me� M hlekki og hlekkjarunu
    //           [y_0,...,y_{M-1}].
    //         Ke�jurnar x og y hafa engan sameiginlegan hlekk.
    // Eftir:  x er l�gleg ke�ja me� N+M hlekki og hlekkjarununa
    //           [x_0,...,x_i,y_0,...,y_{M-1},x_{i+1},...,x_{N-1}].
    //         Taki� eftir a� y rununni er spl�st inn � x rununa
    //         me� i+1 hlekki fyrir framan �r g�mlu x rununni.
    //         Taki� eftir a� leyfilegt er a� y s� t�m runa.
    //         Taki� eftir a� engir n�jir hlekkir ver�a til.
    public static<E> void splice( Link<E> x, int i, Link<E> y )
    {
        // H�r vantar forritstexta me� tveimur lykkjum
        // og vi�eigandi fastayr�ingum. Muni� a� me�h�ndla
        // tilviki� �egar y er t�m ke�ja.
    }
    
    // Notkun: Link<E> x = makeChainLoop(a);
    // Fyrir:  a er E[], ekki null.
    // Eftir:  x er l�gleg ke�ja me� N=a.length hlekki og
    //         hlekkjarunu n�rra hlekkja [h_0,...,h_{N-1}] �annig
    //         a� h_I.head == a[I] fyrir I=0,...,N-1.
    public static<E> Link<E> makeChainLoop( E[] a )
    {
        // H�r vantar forritstexta sem skal reikna
        // �tkomuna � lykkju.
    }
    
    // Notkun: Link<E> x = makeChainRecursive(a,i,j);
    // Fyrir:  a er E[], ekki null, og a[i..j) er sv��i � a.
    //         (Athugi� a� �� er 0 <= i <= j <= a.length).
    // Eftir:  x er l�gleg ke�ja me� N=j-i hlekki og
    //         hlekkjarunu n�rra hlekkja [h_0,...,h_{N-1}] �annig
    //         a� h_I.head == a[I-i] fyrir I=0,...,N-1.
    public static<E> Link<E> makeChainRecursive( E[] a, int i, int j )
    {
        // H�r vantar forritstexta sem skal reikna
        // �tkomuna endurkv�mt.
    }
    
    // Pr�fi� a� keyra �essa skipun:
    //  java E11 1 2 3 4 5 6
    // �a� �tti a� skrifa
    //  1 2 3 4 1 2 3 4 5 6 5 6
    public static void main( String[] args )
    {
        Link<String> x = makeChainLoop(args);
        Link<String> y = makeChainRecursive(args,0,args.length);
        splice(x,3,y);
        splice(x,0,null);
        while( x != null )
        {
            System.out.print(x.head+" ");
            x = x.tail;
        }
    }
}