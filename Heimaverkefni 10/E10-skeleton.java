// Tilvik af E10<T> eru biðraðir gilda af tagi T.
public class E10<T>
{
    static class Link<E>
    {
        public E head;
        public Link<E> tail;
    }
    
    // Athugið: Búa má til nýjan hlekk fyrir gildi
    // af tagi T svona:
    //    Link<T> x = new Link<T>();
    
    Link<T> last;
    
    /* Fastayrðing gagna:
        Skrifið hér fastayrðingu gagna á íslensku
        eða ensku, sem samsvarar fastayrðingunni
        (þ.e. umsögninni Valid()) í Dafny skránni
        H10.dfy.  Reynið að vera stuttorð og nákvæm.
        Nauðsynlegt er að fastayrðingin sé sönn
        eftir smíð hlutar af tagi E10<T> og gefi
        nægilegar upplýsingar til að forritari geti
        útfært smiðinn fyrir E10 og sérhverja af
        aðgerðunum isEmpty(), put(x) og get() án
        þess að vita innviði hinna aðgerðanna.
        Einu nauðsynlegu upplýsingarnar fyrir
        forritara til að útfæra hverja af
        aðgerðunum eru fastayrðing gagna og
        lýsing viðkomandi aðgerðar, þ.e.
        Notkun/Fyrir/Eftir.
        Athugið að fastayrðingin verður að hafa
        tvö tilvik, eitt fyrir tóma biðröð og
        annað fyrir biðröð sem ekki er tóm.
        
        ...
    */
    
    // Notkun: E10<T> q = new E10<T>();
    // Fyrir:  Ekkert (annað en að T er hluttag).
    // Eftir:  q vísar á nýja tóma biðröð hluta af
    //         tagi T.
    public E10()
    {
        ...
    }
    
    // Notkun: ...
    // Fyrir:  ...
    // Eftir:  ...
    public void put( T x )
    {
        ...
    }
    
    // Notkun: ...
    // Fyrir:  ...
    // Eftir:  ...
    public boolean isEmpty()
    {
        ...
    }
    
    // Notkun: ...
    // Fyrir:  ...
    // Eftir:  ...
    public T get()
    {
        ...
    }
    
    // Notkun: Af skipanalínunni:
    //           java E10 1 2 3 4 5
    // Eftir:  Búið er að skrifa
    //           1 2 3 4 5
    //         á aðalúttak.
    public static void main( String[] args )
    {
        E10<String> q = new E10<String>();
        for( int i=0 ; i!=args.length ; i++ ) q.put(args[i]);
        while( !q.isEmpty() ) System.out.print(q.get()+" ");
    }
}