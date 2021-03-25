// Tilvik af H11<T> eru forgangsbi�ra�ir hluta af tagi T.
// Tilvik af H11<T> er a�eins h�gt a� b�a til fyrir klasa T
// sem eru Comparable, �.e. tilvik af T eru samanbur�arh�f hvort
// vi� anna�, me� �eim samningi sem �v� fylgir.

// Skilgreiningar (�etta m� skilgreina formlega � Dafny):
//
//   � fylki a sem inniheldur s�ti i segjum vi� a� s�ti 2*i+1 og
//   2*i+2 s�u b�rn s�tis i, ef �au eru til sta�ar � fylkinu.
//   � svipa�an h�tt segjum vi� a� fyrir s�ti i > 0 s� s�ti
//   floor((i-1)/2) foreldri s�tis i.
//
//   Vi� skilgreinum a� s�ti 2*i+1 og 2*i+2 s�u afkomendur s�tis
//   i og vi� skilgreinum einnig a� ef s�ti k er afkomandi j og
//   j er afkomandi i �� er k afkomandi i (gegnvirkni, transitivity).
//
//   Fyrir sv��i a[i..j) � fylki samanbur�arh�fra gilda segjum vi�
//   a� sv��i� uppfylli hr�guskilyr�i �� og �v� a�eins a� fyrir
//   s�rhver tv� s�ti n og m innan sv��isins, �ar sem m er afkomandi
//   n gildi a� b��i a[m] og a[n] eru l�gleg gildi (ekki null, til
//   d�mis) og a[m] <= a[n], �.e. a[m].compareTo(a[n]) <= 0.
//
//   Vi� segjum einnig a� sv��i a[0..j) s� hr�ga ef sv��i�
//   uppfyllir hr�guskilyr�i.
//
//   Setning: Ef a[i..j) er sv��i � fylki og j < 2*i+1 �� uppfyllir
//   sv��i� hr�guskilyr�i �v� ekkert s�ti innan sv��isins er
//   afkomandi annars s�tis innan sv��isins. Jafngilt skilyr�i er
//   �egar i > floor((j-1)/2) e�a �egar i >= floor((j-1)/2)+1.
//
//   Setning (sannanleg � Dafny): Ef a[0..j) er hr�ga �� er a[0]
//   st�rsta gildi� � sv��inu (ef j != 0, a� sj�lfs�g�u).
//
//   Taki� eftir a� hr�ga a[0..j) er tv�undartr� me� j hn�ta �
//   eins miklu jafnv�gi og h�gt er a� ��last me� j hn�ta tr�.

public class H11< T extends Comparable<? super T>>
{
    private T[] a;
    private int n;
    // draugabreyta multiset<T> m;

    // Fastayr�ing gagna:
    //    ...Skrifi� st��ul�singu h�r sem l�sir �v� hvernig
    //    ...gildin � forgangsbi�r��inni, sem einnig eru gildin
    //    ...� draugabreytunni m, eru geymd fremst � fylkinu a,
    //    ...�annig a� �au mynda hr�gu n gilda.  Muni� a� setja
    //    ...skilyr�i � �tkomur samanbur�a milli vi�eigandi s�ta
    //    ...� sv��inu og setji� skilyr�i sem tengja saman n og
    //    ...a.length.  Reyni� a� sj� til �ess a� ekki �urfi mj�g
    //    ...oft a� endur�thluta a, en sj�i� einnig til �ess a�
    //    ...minniss�un s� ekki �h�fleg.
    //
    //    Muni� a� fastayr�ingin er (� Java, ekki � Dafny) sj�lfgefinn
    //    hluti af eftirskilyr�i allra opinberra a�ger�a, �ar me�
    //    tali� allra smi�a. Einnig er fastayr�ingin sj�lfgefinn
    //    hluti forskilyr�is allra opinberra bo�a annarra en
    //    smi�a.

    // Notkun: H11<T> pq = new H11<T>();
    // Fyrir:  Ekkert (anna� en a� T ver�ur a� vera l�glegt).
    // Eftir:  pq er n� t�m forgangsbi�r�� gilda af tagi T
    //         me� pl�ss fyrir �takmarka�an fj�lda gilda.
    public H11()
    {
        a = (T[]) new Comparable<?>[100];
        n = 0;
    }

    // Notkun: rollDown(a,i,j);
    // Fyrir:  a[i..j) og a[i+1..j) eru sv��i � a.
    //         a[i+1..j) uppfyllir hr�guskilyr�i.
    // Eftir:  a[i..j) inniheldur s�mu gildi og ��ur,
    //         en �eim hefur veri� umra�a� �annig a�
    //         a[i..j) uppfyllir n� hr�guskilyr�i.
    public static<E extends Comparable<? super E>> void rollDown( E[] a, int i, int j )
    {
        // H�r vantar forritstexta
        // H�r �tti a� vera lykkja me� fastayr�ingu sem getur veri�
        // eitthva� a �essa lei�:
        //   ? <= k < ?
        //   Allir samanbur�ir milli s�ta p < q � sv��inu a[i..j)
        //   eru � samr�mi vi� hr�guskilyr�i nema e.t.v. � �eim
        //   tilvikum �egar ???.
    }

    // Notkun: rollUp(a,i,j);
    // Fyrir:  a[i..j) og a[i..j+1) eru sv��i � a.
    //         a[i..j) uppfyllir hr�guskilyr�i.
    // Eftir:  a[i..j+1) inniheldur s�mu gildi og ��ur,
    //         en �eim hefur veri� umra�a� �annig a�
    //         a[i..j+1) uppfyllir n� hr�guskilyr�i.
    public static<E extends Comparable<? super E>> void rollUp( E[] a, int i, int j )
    {
        // H�r vantar forritstexta.
        // H�r �tti a� vera lykkja me� fastayr�ingu sem getur veri�
        // eitthva� a �essa lei�:
        //   ? <= k <= ?
        //   Allir samanbur�ir milli s�ta p < q � sv��inu a[i..j+1)
        //   eru � samr�mi vi� hr�guskilyr�i nema e.t.v. � �eim
        //   tilvikum �egar ???.
    }
    
    // Notkun: sort(a);
    // Fyrir:  a er fylki gilda af tagi E (og E er l�glegt).
    // Eftir:  a hefur veri� ra�a� � vaxandi r��.
    public static<E extends Comparable<? super E>> void sort( E[] a )
    {
        // H�r vantar forritstexta.
        // �etta skal �tf�ra � hra�virkan h�tt, �.e. O(n log(n)),
        // anna�hvort me� �v� a� nota einungis rollDown � tveimur
        // lykkjum, e�a me� �v� a� nota rollUp � einni lykkju og
        // rollDown � annarri lykkju.
    }
    
    // Notkun: int n = pq.count();
    // Fyrir:  pq er forgangsbi�r��.
    // Eftir:  n er fj�ldi gilda � pq.
    public int count()
    {
        // H�r vantar forritstexta.
    }
    
    // Skrifi� l�singu h�r
    // Notkun: ???
    // Fyrir:  ???
    // Eftir:  ???
    public T deleteMax()
    {
        // H�r vantar forritstexta.
        // Noti� rollDown til a� �tf�ra a�ger�ina.
        // Muni� a� uppf�ra einnig draugabreytuna m.
    }
    
    // Skrifi� l�singu h�r
    // Notkun: ???
    // Fyrir:  ???
    // Eftir:  ???
    public void put( T x )
    {
        // H�r vantar forritstexta.
        // Noti� rollUp til a� �tf�ra a�ger�ina.
        // Muni� a� uppf�ra einnig draugabreytuna m.
        // Athugi� a� undir einhverjum kringumst��um �urfi� �i� a�
        // st�kka fylki� a. E�lilegt er �� a� tv�falda st�r�ina.
        // Noti� vi�eigandi fastayr�ingu � lykkjunni �egar �i�
        // afriti� fr� gamla fylkinu yfir � n�ja.
    }

    // Pr�fi� a� keyra 
    //   java H11 1 2 3 4 10 20 30 40
    // �a� �tti a� skrifa
    //   1 10 2 20 3 30 4 40
    //   40 4 30 3 20 2 10 1    
    public static void main( String[] args )
    {
        sort(args);
        for( int i=0 ; i!=args.length ; i++ ) System.out.print(args[i]+" ");
        System.out.println();
        H11<String> pq = new H11<String>();
        for( int i=0 ; i!=args.length ; i++ ) pq.put(args[i]);
        while( pq.count() != 0 ) System.out.print(pq.deleteMax()+" ");
    }
}