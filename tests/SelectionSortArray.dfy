// Author: Snorri Agnarsson, snorri@hi.is

// The following four predicates can be very useful
// in state descriptions during bubblesort and other
// sorts such as insertion sort and selection sort.

// Check whether this state is provable:
//
//  a: | unknown | in ascending order | unknown |
//      ^         ^                    ^         ^
//      0         i                    j      a.Length
//
predicate IsSorted( a: array<int>, i: int, j: int )
    reads a;
{
    0 <= i <= j <= a.Length &&
    forall p,q | i <= p < q < j :: a[p] <= a[q]
}

// IsSortedSeq(a,i,j) is true if and only if it is
// provable that a[i..j] is in ascending order.
predicate IsSortedSeq( a: seq<int>, i: int, j: int )
{
    0 <= i <= j <= |a| &&
    forall p,q | i <= p < q < j :: a[p] <= a[q]
}

// Check whether this state is provable:
//
//  a: | segment A | segment B |
//      ^           ^           ^
//      0           i          a.Length
//
// where every value in segment A is <=
// every value in segment B.
//
predicate IsSegmented( a: array<int>, j: int )
    reads a;
{
    0 <= j <= a.Length &&
    forall p,q | 0 <= p < j && j <= q < a.Length :: a[p] <= a[q] &&
    forall x,y | x in a[..j] && y in a[j..] :: x <= y
}

predicate IsSegmentedSeq( a: seq<int>, j: int )
{
    0 <= j <= |a| &&
    forall p,q | 0 <= p < j && j <= q < |a| :: a[p] <= a[q] &&
    forall x,y | x in a[..j] && y in a[j..] :: x <= y
}

lemma SeqVsArray( a: array<int>, i: int, j: int )
    ensures IsSorted(a,i,j) <==> IsSortedSeq(a[..],i,j);
    ensures IsSegmented(a,i) <==> IsSegmented(a,i);
{}

// Utility method for swapping values in array.
method Swap( a: array<int>, i: int, j: int )
    modifies a;
    requires 0 <= i < j < a.Length;
    ensures multiset(old(a[..])) == multiset(a[..]);
    ensures a[..i] == old(a[..i]);
    ensures a[i+1..j] ==old(a[i+1..j]);
    ensures a[j+1..] == old(a[j+1..]);
    ensures a[i] == old(a[j]);
    ensures a[j] == old(a[i]);
{
    var tmp := a[i];
    a[i] := a[j];
    assert a[..i] == old(a[..i]);
    assert a[i+1..] ==old(a[i+1..]);
    a[j] := tmp;
}

// Selection sort
method Sort( a: array<int> )
    modifies a;
    ensures multiset(a[..]) == old(multiset(a[..]));
    ensures IsSorted(a,0,a.Length);
{
    var j := 0;
    while j < a.Length-1
        //
        // a: | minnstu í vaxandi röð | stærstu |
        //     ^                       ^         ^
        //     0                       j      a.Length
        //
        invariant 0 <= j <= a.Length;
        decreases a.Length-j;
        invariant multiset(a[..]) == old(multiset(a[..]));
        invariant IsSorted(a,0,j);
        invariant forall p,q | 0 <= p < j <= q < a.Length :: a[p] <= a[q];
    {
        var k := j;
        var i := j+1;
        ghost var preseq := a[..];
        while i != a.Length
            //
            // a: | minnstu í vaxandi röð |     stærstu     |
            //     ^                       ^     ^   ^       ^
            //     0                       j     k   i    a.Length
            //
            //               a[k] er minnst af a[j..i)
            //
            invariant j <= k < i <= a.Length;
            invariant forall p | j <= p < i :: a[k] <= a[p];
            invariant a[..] == preseq;
        {
            if a[i] < a[k] { k := i; }
            i := i+1;
        }
        if j != k
        {
            ghost var a' := a[..];
            Swap(a,j,k);
            SelectionSortSwappingLemma(a',j,k,a[..]);
        }
        j := j+1;
    }
}

lemma SelectionSortSwappingLemma( a: seq<int>, j: int, k: int, a': seq<int> )
    requires 0 <= j < k < |a|;
    requires IsSortedSeq(a,0,j);
    requires IsSegmentedSeq(a,j);
    requires a' == a[..j]+a[k..k+1]+a[j+1..k]+a[j..j+1]+a[k+1..];
    requires forall q | j <= q < |a| :: a[k] <= a[q];
    ensures |a| == |a'|;
    ensures multiset(a) == multiset(a');
    ensures IsSortedSeq(a',0,j+1);
    ensures IsSegmentedSeq(a',j+1);
{
    assert a[..j]+a[j..j+1] == a[..j+1];
    assert a[..j+1]+a[j+1..k] == a[..k];
    assert a[..k]+a[k..k+1] == a[..k+1];
    assert a[..k+1]+a[k+1..] == a;
    calc ==
    {
        multiset(a');
        multiset(a[..j]+a[k..k+1]+a[j+1..k]+a[j..j+1]+a[k+1..]);
        multiset(a[..j])+multiset(a[k..k+1])+multiset(a[j+1..k])+multiset(a[j..j+1])+multiset(a[k+1..]);
        multiset(a[..j])+multiset(a[j+1..k])+multiset(a[j..j+1])+multiset(a[k..k+1])+multiset(a[k+1..]);
        multiset(a[..j])+multiset(a[j..j+1])+multiset(a[j+1..k])+multiset(a[k..k+1])+multiset(a[k+1..]);
        multiset(a[..j]+a[j..j+1]+a[j+1..k]+a[k..k+1]+a[k+1..]);
        multiset(a);
    }
}

method Main()
{
    var s := [1,2,3,1,2,3,1,2,3];
    var a := new int[|s|];
    var i := 0;
    while i != |s|
        decreases |s|-i;
        invariant 0 <= i <= |s|;
        invariant a[0..i] == s[0..i];
    {
        a[i] := s[i];
        i := i+1;
    }
    assert a[..] == s;
    Sort(a);
    assert IsSorted(a,0,a.Length);
    assert multiset(a[..]) == multiset(s);
    print a[..];
}