// Author: Snorri Agnarsson, snorri@hi.is

predicate IsAncestorOf( p: int, q: int )
    decreases q;
    requires 0 <= p;
    requires 0 <= q;
{
    if p >= q then
        false
    else if p == (q-1)/2 then
        true
    else
        IsAncestorOf(p,(q-1)/2)
}

lemma TransitiveAncestor( p: int, q: int, r: int )
    decreases r;
    requires 0 <= p;
    requires 0 <= q;
    requires 0 <= r;
    requires IsAncestorOf(p,q);
    requires IsAncestorOf(q,r);
    ensures  IsAncestorOf(p,r);
{
    if q == (r-1)/2 { return; }
}

predicate IsMinHeap( a: seq<int>, i: int, j: int )
    requires 0 <= i <= j <= |a|;
{
    forall p,q |    i <= p < q < j &&
                    IsAncestorOf(p,q) ::
                        a[p] <= a[q]
}

predicate IsMinHeapRollingDown( a: seq<int>, i: int, k: int, j: int )
    requires 0 <= i <= k < j <= |a|;
{
    forall p,q |    i <= p < q < j &&
                    IsAncestorOf(p,q) &&
                    p != k ::
                        a[p] <= a[q]
}

method RollDownMinHeap( a: array<int>, i: int, j: int )
    modifies a;
    requires 0 <= i < j <= a.Length;
    requires IsMinHeap(a[..],i+1,j);
    ensures IsMinHeap(a[..],i,j);
    ensures multiset(a[..]) == old(multiset(a[..]));
    ensures a[..i] == old(a[..i]);
    ensures a[j..] == old(a[j..]);
    ensures multiset(a[i..j]) == old(multiset(a[i..j]));
{
    var k := i;
    while true
        decreases j-k;
        invariant i <= k < j;
        invariant IsMinHeapRollingDown(a[..],i,k,j);
        invariant multiset(a[..]) == old(multiset(a[..]));
        invariant a[..i] == old(a[..i]);
        invariant a[j..] == old(a[j..]);
        invariant multiset(a[i..j]) == old(multiset(a[i..j]));
    {
        var c := 2*k+1;
        if c >= j { return; }
        if c+1 < j && a[c+1] < a[c] { c := c+1; }
        if a[k] <= a[c] { return; }
        assert i <= k < c < j;
        assert multiset(a[i..j]) == old(multiset(a[i..j]));
        ghost var tmp1 := a[i..j];
        ghost var tmp2 := multiset(a[i..j]);
        a[k], a[c] := a[c], a[k];
        assert multiset(a[i..j]) == tmp2;
        assert multiset(a[i..j]) == multiset(tmp1);
        assert multiset(a[i..j]) == old(multiset(a[i..j]));
        k := c;
        assert IsMinHeapRollingDown(a[..],i,k,j);
    }
}

predicate IsMinHeapRollingUp( a: seq<int>, i: int, k: int, j: int )
    requires 0 <= i <= k < j <= |a|;
{
    forall p,q |    i <= p < q < j &&
                    IsAncestorOf(p,q) &&
                    q != k ::
                        a[p] <= a[q]
}

method RollUpMinHeap( a: array<int>, j: int )
    modifies a;
    requires 0 <= j < a.Length;
    requires IsMinHeap(a[..],0,j);
    ensures IsMinHeap(a[..],0,j+1);
    ensures multiset(a[..]) == old(multiset(a[..]));
    ensures a[j+1..] == old(a[j+1..]);
    ensures multiset(a[0..j+1]) == old(multiset(a[0..j+1]));
{
    var k := j;
    while true
        decreases k;
        invariant 0 <= k <= j;
        invariant IsMinHeapRollingUp(a[..],0,k,j+1);
        invariant multiset(a[..]) == old(multiset(a[..]));
        invariant a[j+1..] == old(a[j+1..]);
        invariant multiset(a[0..j+1]) == old(multiset(a[0..j+1]));
    {
        if k == 0 { return; }
        var c := (k-1)/2;
        if a[k] >= a[c] { return; }
        assert IsAncestorOf(c,k);
        a[k], a[c], k := a[c], a[k], c;
        assert IsMinHeapRollingUp(a[..],0,k,j+1);
    }
}

lemma PartOfHeap( a: seq<int>, i: int, j: int, p: int, q: int )
    requires 0 <= i <= p <= q <= j <= |a|;
    requires IsMinHeap(a,i,j);
    ensures IsMinHeap(a,p,q);
{}

lemma ZeroIsRoot( p: int )
    decreases p;
    requires p > 0;
    ensures IsAncestorOf(0,p);
{
    if p == 1 || p == 2 { return; }
    ZeroIsRoot((p-1)/2);
    TransitiveAncestor(0,(p-1)/2,p);
}

lemma RootHasMin( a: seq<int>, i: int, j: int )
    requires 0 <= i <= j <= |a|;
    requires IsMinHeap(a,i,j);
    ensures forall p | i <= p < j && IsAncestorOf(i,p) :: a[i] <= a[p];
{}

lemma ZeroHasMin( a: seq<int>, n: int )
    requires 0 < n <= |a|;
    requires IsMinHeap(a,0,n);
    ensures forall p | 0 <= p < n :: a[0] <= a[p];
{
    if n == 0 { return; }
    if n == 1 { return; }
    if n == 2 { return; }
    RootHasMin(a,1,n);
    RootHasMin(a,2,n);
    assert a[0] <= a[1];
    assert a[0] <= a[2];
    assert forall p | 2 < p < n :: IsAncestorOf(1,p) || IsAncestorOf(2,p);
}