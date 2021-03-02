// Höfundur: Snorri Agnarsson, snorri@hi.is

include "IntQueue.dfy"
include "Chain.dfy"

// Þessi biðraðarklasi notar eintengda lista
// breytanlegra hlekkja.
class IntQueueChain extends IntQueue
{
    var first: Link?<int>;
    var last: Link?<int>;
    ghost var linkseq: seq<Link<int>>;

    // q.Valid() er satt þá og því aðeins að
    // eftirfarandi fastayrðing gagna sé sönn.
    // Biðröðin inniheldur tölurnar í keðju
    // hlekkja af tagi Link<int>. Ef biðröðin
    // er tóm þá er first==last==null. Ef ekki,
    // þá bendir first á fremsta hlekk keðjunnar
    // og last bendir á síðasta hlekk keðjunnar.
    // Fremsti hlekkurinn inniheldur fremsta gildi
    // biðraðarinnar og inniheldur bendi á næsta
    // hlekk (ef einhver er), sem inniheldur næsta
    // gildi, og svo koll af kolli. Aftasti
    // hlekkurinn inniheldur ekki bendi á annan
    // hlekk heldur null bendi í þess stað.
    // Auk þess þurfa draugabreyturnar Repr og
    // ghostseq að innihalda gildi sem samsvara
    // þessu ástandi, og einnig draugabreytan
    // linkseq sem inniheldur runu allra hlekkjanna
    // í keðjunni í röð sem samsvarar ghostseq.
    predicate Valid()
        reads this, Repr;
    {
        (forall z | z in linkseq :: z in Repr) &&
        (forall z | z in Repr :: z in linkseq) &&
        (ghostseq == ValueSeq(linkseq)) &&
        (first == null ==>
            last == null &&
            linkseq == []
        ) &&
        (first != null ==>
            last != null &&
            linkseq != [] &&
            first in Repr &&
            last in Repr &&
            first.Valid(linkseq) &&
            last.Valid([last]) &&
            first == linkseq[0] &&
            last == linkseq[|linkseq|-1] &&
            last.tail == null &&
            forall i | 0 <= i < |linkseq|-1 ::
                linkseq[i].tail == linkseq[i+1]
        ) &&
        (forall p,q | 0 <= p < q < |linkseq| ::
            linkseq[p] != linkseq[q]
        )
    }

    constructor()
        ensures Valid();
        ensures Repr == {};         // <-- þrenging eftirskilyrðis
        ensures ghostseq == [];
    {
        first := null;
        last := null;
        Repr := {};
        ghostseq := [];
        linkseq := [];
    }

    predicate method IsEmpty()
        reads this, Repr;
        requires Valid();
        ensures IsEmpty() <==> ghostseq==[];
    {
        first == null
    }
    
    method Put( x: int )
        modifies this, Repr;
        requires Valid();
        ensures Valid() && fresh(Repr-old(Repr));
        ensures ghostseq == old(ghostseq)+[x];
    {
        first, linkseq, last := Append1(first,linkseq,last,x);
        Repr := Repr+{last};
        ghostseq := ghostseq+[x];
    }
    
    method Get() returns ( x: int )
        modifies this;                          // <-- þrenging eftirskilyrðis
        requires Valid();
        requires ghostseq != [];
        ensures Valid() && Repr < old(Repr);    // <-- þrenging eftirskilyrðis
        ensures ghostseq == old(ghostseq[1..]);
        ensures x == old(ghostseq[0]);
    {
        ValueSeqLemma(linkseq,ghostseq);
        x := first.head;
        Repr := Repr-{first};
        ghostseq := ghostseq[1..];
        linkseq := linkseq[1..];
        first := first.tail;
        if first == null { last := null; }
    }
}

method Factory() returns ( q: IntQueue )
    ensures fresh(q);
    ensures fresh(q.Repr);
    ensures q.Valid();
    ensures q.IsEmpty();
{
    q := new IntQueueChain();
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