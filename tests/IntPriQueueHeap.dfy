// Höfundur: Snorri Agnarsson, snorri@hi.is

trait IntPriQueue
{
    ghost var ghostbag: multiset<int>;
    ghost var Repr: set<object>;

    predicate Valid()
        reads this, Repr;

    predicate method IsEmpty()
        reads this, Repr;
        requires Valid();
        ensures IsEmpty() <==> |ghostbag| == 0;
    
    method Add( x: int )
        modifies this, Repr;
        requires Valid();
        ensures Valid() && fresh(Repr-old(Repr));
        ensures ghostbag == old(ghostbag)+multiset{x};
    
    method RemoveMax() returns ( x: int )
        modifies this, Repr;
        requires Valid();
        requires |ghostbag| != 0;
        ensures Valid() && fresh(Repr-old(Repr));
        ensures x in old(ghostbag);
        ensures ghostbag == old(ghostbag)-multiset{x};
        ensures forall z | z in ghostbag :: x >= z;
}

method Sort( s: seq<int> ) returns( r: seq<int> )
    ensures multiset(s) == multiset(r);
    ensures forall p,q | 0 <= p < q < |r| :: r[p] <= r[q];
{
    var p := new IntPriQueueTree();
    var i := 0;
    while i != |s|
        invariant 0 <= i <= |s|;
        invariant p.ghostbag == multiset(s[..i]);
    {
        p.Add(s[i]);
        i := i+1;
    }
    r := [];
    while !p.IsEmpty()
        invariant multiset(s) == p.ghostbag+multiset(r);
        invariant forall p,q | 0 <= p < q < |r| :: r[p] <= r[q];
        invariant forall x,y | x in p.ghostbag && y in r :: y >= x;
    {
        var x := p.RemoveMax();
        r := [x]+r;
    }
}

method Main()
{
    var r := Sort([9,1,8,2,7,3,6,4,5,9,1,8,2,7,3,6,4,5]);
    print r;
}