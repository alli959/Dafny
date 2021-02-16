// Höfundur: Snorri Agnarsson, snorri@hi.is

trait IntQueue
{
    ghost var ghostseq: seq<int>;
    ghost var Repr: set<object>;

    predicate Valid()
        reads this, Repr;

    predicate method IsEmpty()
        reads this, Repr;
        requires Valid();
        ensures IsEmpty() <==> ghostseq==[];
    
    method Put( x: int )
        modifies this, Repr;
        requires Valid();
        ensures Valid() && fresh(Repr-old(Repr));
        ensures ghostseq == old(ghostseq)+[x];
    
    method Get() returns ( x: int )
        modifies this, Repr;
        requires Valid();
        requires ghostseq != [];
        ensures Valid() && fresh(Repr-old(Repr));
        ensures ghostseq == old(ghostseq[1..]);
        ensures x == old(ghostseq[0]);
}