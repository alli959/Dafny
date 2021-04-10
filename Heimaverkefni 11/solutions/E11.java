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
        if( y == null ) return;
        int k = 0;
        while( k != i )
            // 0 <= k <= i.
            // x v�sar � hlekk n�mer k � upphaflegu
            // hlekkjake�ju x.
        {
            x = x.tail;
            k++;
        }
        Link<E> z = x.tail;
        x.tail = y;
        // z er l�gleg ke�ja me� hlekkjarununni
        //  [x_{i+1},...,x_{N-1}], mi�a� vi� upphaflega x.
        // x er l�gleg ke�ja me� hlekkjarununni
        //  [x_0,...,x_i,y_0,...,y_{M-1}].
        // y er �breytt og er ekki t�m.
        while( y.tail != null )
            // y v�sar � einhvern hlekk � upphaflega y,
            // sem er �� einnig hlekkur � n�verandi x.
            // x og z eru eins og l�st er a� ofan.
        {
            y = y.tail;
        }
        y.tail = z;
    }
    
    // Notkun: Link<E> x = makeChainLoop(a);
    // Fyrir:  a er E[], ekki null.
    // Eftir:  x er l�gleg ke�ja me� N=a.length hlekki og
    //         hlekkjarunu n�rra hlekkja [h_0,...,h_{N-1}] �annig
    //         a� h_I.head == a[I] fyrir I=0,...,N-1.
    public static<E> Link<E> makeChainLoop( E[] a )
    {
        int i = a.length;
        Link<E> r = null;
        while( i != 0 )
            // e er l�gleg ke�ja N==a.length-i n�rra hlekkja og hlekkjarunu
            // [h_0,...,h_{N-1}] �annig a� fyrir k=0,...,N-1 gildir a�
            // h_k.head == a[i+k].
        {
            Link<E> tmp = new Link<E>();
            tmp.tail = r;
            tmp.head = a[--i];
            r = tmp;
        }
        return r;
    }
    
    // Notkun: Link<E> x = makeChainRecursive(a,i,j);
    // Fyrir:  a er E[], ekki null, og a[i..j) er sv��i � a.
    //         (Athugi� a� �� er 0 <= i <= j <= a.length).
    // Eftir:  x er l�gleg ke�ja me� N=j-i hlekki og
    //         hlekkjarunu n�rra hlekkja [h_0,...,h_{N-1}] �annig
    //         a� h_I.head == a[I-i] fyrir I=0,...,N-1.
    public static<E> Link<E> makeChainRecursive( E[] a, int i, int j )
    {
        if( i == j ) return null;
        Link<E> r = new Link<E>();
        r.tail = makeChainRecursive(a,i+1,j);
        r.head = a[i];
        return r;
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
        while( x != null )
        {
            System.out.print(x.head+" ");
            x = x.tail;
        }
    }
}