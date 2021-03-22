// Höfundur spurningar:  Snorri Agnarsson, snorri@hi.is
// Permalink spurningar: https://rise4fun.com/Dafny/Nmmuq

// Höfundur lausnar:     ...
// Permalink lausnar:    ...

// Klárið að forrita klasann QueueCycleChain
// með því að forrita stofnana á aðferðunum
// IsEmpty, Put og Get, ásamt smiðnum fyrir
// klasann.
// Allt sem til þarf er í þessari skrá og þið
// ættuð ekki að þurfa að kalla á neinar
// hjálparsetningar eða setja nein assert.
// Athugið að ósennilegt er að unnt sé að
// vinna þetta verkefni á rise4fun vefsíðunni.

class QueueCycleChain<T> extends Queue<T>
{
    var last: Link?<T>;
    ghost var cycle: seq<Link<T>>;

    predicate Valid()
        reads this, Repr;
    {
        (last != null ==> last in Repr) &&
        (forall z | z in cycle :: z in Repr) &&
        (forall z | z in Repr :: z in cycle) &&
        (ghostseq == ValueSeq(cycle)) &&
        (last == null ==> cycle == []) &&
        (last != null ==> last.ValidCycle(cycle)) &&
        (|cycle| == |ghostseq|) &&
        (forall i | 0 <= i < |cycle| :: cycle[i].head == ghostseq[i])
    }

    constructor()
        ensures Valid();
        ensures Repr == {};
        ensures ghostseq == [];
    {
        // Gefum tilviksbreytunum last, Repr, ghostseq og cycle
        // rétt gildi miðað við fastayrðingu gagna og eftirskilyrði.
        last := cycle[|cycle|-1];
        
        assert  // Þetta assert er sama og fastayrðing gagna
                // og er óþarfi ef smiðurinn er rétt forritaður,
                // en ef ekki þá hjálpar þetta að finna villur.
            (last != null ==> last in Repr) &&
            (forall z | z in cycle :: z in Repr) &&
            (forall z | z in Repr :: z in cycle) &&
            (ghostseq == ValueSeq(cycle)) &&
            (last == null ==> cycle == []) &&
            (last != null ==> last.ValidCycle(cycle)) &&
            |cycle| == |ghostseq| &&
            (forall i | 0 <= i < |cycle| :: cycle[i].head == ghostseq[i]);
    }

    predicate method IsEmpty()
        reads this, Repr;
        requires Valid();
        ensures IsEmpty() <==> ghostseq==[];
    {
        ...
    }
    
    method Put( x: T )
        modifies this, Repr;
        requires Valid();
        ensures Valid();
        ensures fresh(Repr-old(Repr));
        ensures ghostseq == old(ghostseq)+[x];
    {
        ...
    }
    
    method Get() returns ( x: T )
        modifies this, Repr;
        requires Valid();
        requires ghostseq != [];
        ensures Valid();
        ensures Repr < old(Repr);
        ensures ghostseq == old(ghostseq[1..]);
        ensures x == old(ghostseq[0]);
    {
        ...
    }
}

///////////////////////////////////////////////////////////////
// Hér lýkur breytanlega hluta skrárinnar.
// Ekki breyta því sem er hér fyrir neðan.
///////////////////////////////////////////////////////////////

// Hér er grunnskilgreiningin á hegðun biðraðar.
trait Queue<T>
{
    ghost var ghostseq: seq<T>;
    ghost var Repr: set<object>;

    predicate Valid()
        reads this, Repr;

    predicate method IsEmpty()
        reads this, Repr;
        requires Valid();
        ensures IsEmpty() <==> ghostseq==[];
    
    method Put( x: T )
        modifies this, Repr;
        requires Valid();
        ensures Valid() && fresh(Repr-old(Repr));
        ensures ghostseq == old(ghostseq)+[x];
    
    method Get() returns ( x: T )
        modifies this, Repr;
        requires Valid();
        requires ghostseq != [];
        ensures Valid() && fresh(Repr-old(Repr));
        ensures ghostseq == old(ghostseq[1..]);
        ensures x == old(ghostseq[0]);
}

// Hér er skilgreiningin á breytanlegum hlekkjum
// sem notaðir eru í hringtengdum keðjum.
class Link<T>
{
    var head: T;
    var tail: Link<T>;
    
    // x.ValidCycle(cycle) er satt þá og því aðeins
    // að x vísi á aftasta hlekk í hringkeðju þeirra
    // hlekkja sem chain inniheldur. Aftasti
    // hlekkurinn í þeirri keðju verður að hafa
    // tail sem vísar á fremsta.
    predicate ValidCycle( cycle: seq<Link<T>> )
        reads this, cycle;
    {
        |cycle| > 0 &&
        this == cycle[|cycle|-1] &&
        tail == cycle[0] &&
        tail.ValidSequence(cycle) &&
        forall p,q | 0 <= p < q < |cycle| ::
            cycle[p] != cycle[q]
    }
    
    // x.ValidSequence(s) er satt þá og því aðeins að
    // hlekkurinn x sé sá fremsti í keðju hlekkjanna
    // í rununni s og að keðjan sé tengd í þeirri röð.
    predicate ValidSequence( sequence: seq<Link<T>> )
        reads this, sequence;
    {
        |sequence| > 0 &&
        this == sequence[0] &&
        forall i | 0 <= i < |sequence|-1 ::
            sequence[i].tail == sequence[i+1]
    }
    
    // Smiðurinn gerir okkur kleift að skeyta nýjum hlekk
    // inn í hringkeðju, sem gefur þá lengri hringkeðju
    // með nýjum aftasta hlekk.
    // Þessi smiður virkar á þægilegan hátt miðað við
    // fastayrðingu gagna í klasanum QueueCycleChain.
    
    // Notkun: Link<T> y := new Link(h,x,cycle,values);
    // Fyrir:  x er Link?<T> og ef x er null þá eru
    //         runurnar cycle og values báðar tómar.
    //         Annars vísar x á aftasta hlekk í hringkeðju
    //         hlekkjanna í cycle, sem innihalda gildin
    //         í values.
    // Eftir:  y vísar á nýjan hlekk í hringkeðju sem
    //         inniheldur alla hlekkina úr x, ásamt þessum
    //         nýja hlekk.  Ef x er null þá inniheldur
    //         þessi hringkeðja aðeins þann eina hlekk,
    //         annars var nýja hlekknum skeytt inn fyrir
    //         aftan hlekkinn sem x bendir á.
    constructor( h: T, x: Link?<T>, ghost cycle: seq<Link<T>>, ghost values: seq<T> )
        modifies if cycle != [] then {cycle[|cycle|-1]} else {};
        requires (x == null && cycle == []) || (x != null && x.ValidCycle(cycle));
        requires values == ValueSeq(cycle);
        requires forall i | 0 <= i < |cycle| :: cycle[i].head == values[i];
        ensures head == h;
        ensures tail == if x == null then this else cycle[0];
        ensures fresh(this);
        ensures forall i | 0 <= i < |cycle| :: cycle[i].head == values[i];
        ensures forall i | 0 <= i < |cycle| :: cycle[i].head == old(cycle[i].head);
        ensures forall z | z in cycle :: z.head == old(z.head);
        ensures ValueSeq(cycle) == values;
        ensures ValidCycle(cycle+[this]);
        ensures ValueSeq(cycle+[this]) == values+[h];
    {
        head := h;
        tail := this;
        new;
        if x != null
        {
            tail := x.tail;
            x.tail := this;
            HeadsEqual(old(cycle),cycle,values);
            AppendLink(cycle,this);
        }
    }    
}

// Fallið RemoveFirst gerir okkur kleift að fjarlægja
// viðeigandi hlekk úr hringkeðju hlekkja. Virkni þessa
// falls er þægileg miðað við fastayrðingu gagna í
// klasanum QueueCycleChain.
method RemoveFirst<T>   ( last: Link<T>
                        , ghost cycle: seq<Link<T>>
                        , ghost vals: seq<T>
                        )
        returns ( newlast: Link?<T>
                , ghost newcycle: seq<Link<T>>
                , ghost newvals: seq<T>
                )
    modifies last;
    requires last.ValidCycle(cycle);
    requires ValueSeq(cycle) == vals;
    requires |vals| == |cycle|;
    requires |vals| > 0;
    ensures last.head == old(last.head);
    ensures |vals| == 1 ==>
                    newlast == null &&
                    newcycle == [] &&
                    newvals == [];
    ensures |vals| > 1 ==>
                    newlast == last &&
                    newcycle == cycle[1..] &&
                    newlast.ValidCycle(cycle[1..]) &&
                    newvals == vals[1..] &&
                    ValueSeq(newcycle) == newvals;
{
    if last.tail == last
    {
        newlast := null;
        newcycle := [];
        newvals := [];
        return;
    }
    ValueSeqHeads(cycle,vals);
    newlast := last;
    newcycle := cycle[1..];
    newvals := vals[1..];
    newlast.tail := newlast.tail.tail;
    HeadsEqual(old(cycle[1..]),cycle[1..],vals[1..]);
}

function ValueSeq<T>( x: seq<Link<T>> ): seq<T>
    reads x;
    ensures |x| == |ValueSeq(x)|;
{
    if x == [] then
        []
    else
        [x[0].head]+ValueSeq(x[1..])
}

lemma ValueSeqHeads<T>( x: seq<Link<T>>, v: seq<T> )
    requires v == ValueSeq(x);
    ensures forall i | 0 <= i < |x| :: x[i].head == v[i];
{
    if |x| == 0 { return; }
    ValueSeqHeads(x[1..],v[1..]);
}

lemma AppendLink<T>( x: seq<Link<T>>, z: Link<T> )
    ensures ValueSeq(x+[z]) == ValueSeq(x)+[z.head];
{
    if x == [] { return; }
    AppendLink(x[1..],z);
    calc ==
    {
        x+[z];
        (x[..1]+x[1..])+[z];
        x[..1]+(x[1..]+[z]);
    }
}

lemma HeadsEqual<T>( x: seq<Link<T>>, y: seq<Link<T>>, v: seq<T> )
    requires |x| == |y| == |v|;
    requires forall i | 0 <= i < |x| :: x[i].head == v[i] == y[i].head;
    ensures ValueSeq(x) == v == ValueSeq(y);
{
    if |x| == 0 { return; }
    HeadsEqual(x[1..],y[1..],v[1..]);
}

method Factory() returns ( q: Queue<int> )
    ensures fresh(q);
    ensures fresh(q.Repr);
    ensures q.Valid();
    ensures q.IsEmpty();
{
    q := new QueueCycleChain<int>();
}

method Main()
{
    var q1 := Factory();
    var q2 := Factory();
    var q3 := Factory();
    var q4 := Factory();
    q1.Put(1);
    q2.Put(1);
    q3.Put(1);
    q4.Put(1);
    q1.Put(2);
    assert q1.ghostseq == [1,2];
    q2.Put(2);
    q3.Put(2);
    q4.Put(2);
    var x;
    x := q1.Get(); print x; print " ";
    assert x == 1;
    x := q1.Get(); print x; print " ";
    assert x == 2;
    assert q1.ghostseq == [];
    x := q2.Get(); print x; print " ";
    x := q2.Get(); print x; print " ";
    x := q3.Get(); print x; print " ";
    x := q3.Get(); print x; print " ";
    x := q4.Get(); print x; print " ";
    x := q4.Get(); print x; print " ";
    assert q1.IsEmpty();
    assert q2.IsEmpty();
    assert q3.IsEmpty();
    assert q4.IsEmpty();
}