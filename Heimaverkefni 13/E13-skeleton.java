public class E13
{
	// Notkun: int q = partition(a,i,j);
	// Fyrir:  a[i..j) er ekki-tómt svæði sem inniheldur
	//         löglega E hluti.
	// Eftir:  i <= q < j.
	//         Svæðið a[i..j) inniheldur sömu hluti eftir
	//         sem áður, en búið er að endurraða þeim þ.a.
	//         a[i..q) <= a[q] <= a(q..j).
	public static<E extends Comparable<? super E>>
	int partition( E[] a, int i, int j )
	{
		// Hér vantar útfærslu.
		// Eðlilegt er að nota lykkju og einhverja aðferð
		// sem auðvelt er að rökstyðja með fastayrðingu.
		// Aðferð Lomutos er trúlega auðveldust.
	}

	// Notkun: quickSelectRecursive(a,i,k,j);
	// Fyrir:  0 <= i <= k < j <= a.length.
	//         Svæðið a[i..j) inniheldur löglega E hluti.
	// Eftir:  Svæðið a[i..j) inniheldur sömu hluti, en
	//         búið er að endurraða þannig að
	//           a[i..k) <= a[k] <= a(k..j).
	public static<E extends Comparable<? super E>>
	void quickSelectRecursive( E[] a, int i, int k, int j )
	{
		// Hér vantar útfærslu sem skal vera endurkvæm
		// og án lykkju.
		// Notið fallið partition að ofan.
        // Ekki skal fullraða svæðinu.
        // Eðlileg útfærsla mun hafa meðaltímaflækju
        // O(n) fyrir slembin gögn.
	}

    // Sama lýsing og að ofan, fyrir utan nafn fallsins.
	public static<E extends Comparable<? super E>>
	void quickSelectLoop( E[] a, int i, int k, int j )
	{
		// Hér vantar útfærslu sem skal vera án endurkvæmni.
		// Notið lykkju til að þrengja að sætinu k.
		// Notið fallið partition að ofan.
		// Munið að skrifa skýra og skilmerkilega fastayrðingu.
        // Ekki skal fullraða svæðinu.
        // Eðlileg útfærsla mun hafa meðaltímaflækju
        // O(n) fyrir slembin gögn.
	}
    
    public static void main( String[] args )
    {
        int k = Integer.parseInt(args[0]);
        if( k < 1 || k >= args.length ) throw new Error("Invalid input index");
        quickSelectLoop(args,1,k,args.length);
        for( int i = 1 ; i != args.length ; i++ ) System.out.println(args[i]+" ");
    }
}