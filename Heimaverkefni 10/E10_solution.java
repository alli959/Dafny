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
        
        Tóm biðröð er táknuð með last == null.
        Biðröð sem ekki er tóm og inniheldur
        gildi v1,v2,...,vN, frá fremsta gildi
        til aftasta, er geymd sem hringkeðja
        hlekkja sem innihalda gildin, þar sem
        hlekkurinn sem inniheldur v1 vísar á
        (gegnum tail) hlekkinn sem inniheldur
        v2, sem vísar a v3 og svo koll af kolli.
        Hlekkur vN vísar á hlekk v1 og þannig
        myndast hringur.
        Tilviksbreytan last vísar á hlekk vN,
        þ.e. aftasta hlekk keðjunnar, sem síðan
        vísar á fremsta.
    */
    
    // Notkun: E10<T> q = new E10<T>();
    // Fyrir:  Ekkert (annað en að T er hluttag).
    // Eftir:  q vísar á nýja tóma biðröð hluta af
    //         tagi T.
    public E10()
    {
        last = null;
    }
    
    // Notkun: q.put(x);
    // Fyrir:  Ekkert (annað en sjálfsögðu skilyrðin
    //         að q er ekki null og bæði q og x eru
    //         af réttu tagi, þ.e. q er E10<T> og x
    //         er T.
    // Eftir:  Búið er að bæta x aftast í biðröðina q.
    public void put( T x )
    {
        Link<T> newLast = new Link<T>();
        newLast.head = x;
        if( last == null )
        {
            last = newLast;
            last.tail = last;
            return;
        }
        newLast.tail = last.tail;
        last.tail = newLast;
        last = newLast;
    }
    
    // Notkun: boolean b = q.isEmpty();
    // Fyrir:  Ekkert (annað en að q er ekki null).
    // Eftir:  b er satt þá og því aðeins að q sé
    //         ekki tóm.
    public boolean isEmpty()
    {
        return last == null;
    }
    
    // Notkun: T x = q.get();
    // Fyrir:  q er ekki tóm.
    // Eftir:  Fremsta gildið sem var í q hefur
    //         verið fjarlægt og er í x.
    public T get()
    {
        T x = last.tail.head;
        if( last.tail == last )
        {
            last = null;
            return x;
        }
        last.tail = last.tail.tail;
        return x;
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