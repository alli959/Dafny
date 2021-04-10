// Klasinn E11 notar klasann Link sem er í Link.java.
// Lesið skilgreiningarnar og setningarnar þar.

public class E11
{    
    // Notkun: splice(x,i,y);
    // Fyrir:  x er lögleg keðja með N hlekki og hlekkjarunu
    //           [x_0,...,x_{N-1}].
    //         0 <= i < N.
    //         y er lögleg keðja með M hlekki og hlekkjarunu
    //           [y_0,...,y_{M-1}].
    //         Keðjurnar x og y hafa engan sameiginlegan hlekk.
    // Eftir:  x er lögleg keðja með N+M hlekki og hlekkjarununa
    //           [x_0,...,x_i,y_0,...,y_{M-1},x_{i+1},...,x_{N-1}].
    //         Takið eftir að y rununni er splæst inn í x rununa
    //         með i+1 hlekki fyrir framan úr gömlu x rununni.
    //         Takið eftir að leyfilegt er að y sé tóm runa.
    //         Takið eftir að engir nýjir hlekkir verða til.
    public static<E> void splice( Link<E> x, int i, Link<E> y )
    {
        // Hér vantar forritstexta með tveimur lykkjum
        // og viðeigandi fastayrðingum. Munið að meðhöndla
        // tilvikið þegar y er tóm keðja.
    }
    
    // Notkun: Link<E> x = makeChainLoop(a);
    // Fyrir:  a er E[], ekki null.
    // Eftir:  x er lögleg keðja með N=a.length hlekki og
    //         hlekkjarunu nýrra hlekkja [h_0,...,h_{N-1}] þannig
    //         að h_I.head == a[I] fyrir I=0,...,N-1.
    public static<E> Link<E> makeChainLoop( E[] a )
    {
        // Hér vantar forritstexta sem skal reikna
        // útkomuna í lykkju.
    }
    
    // Notkun: Link<E> x = makeChainRecursive(a,i,j);
    // Fyrir:  a er E[], ekki null, og a[i..j) er svæði í a.
    //         (Athugið að þá er 0 <= i <= j <= a.length).
    // Eftir:  x er lögleg keðja með N=j-i hlekki og
    //         hlekkjarunu nýrra hlekkja [h_0,...,h_{N-1}] þannig
    //         að h_I.head == a[I-i] fyrir I=0,...,N-1.
    public static<E> Link<E> makeChainRecursive( E[] a, int i, int j )
    {
        // Hér vantar forritstexta sem skal reikna
        // útkomuna endurkvæmt.
    }
    
    // Prófið að keyra þessa skipun:
    //  java E11 1 2 3 4 5 6
    // það ætti að skrifa
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