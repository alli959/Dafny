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

// Insertion sort
method Sort( a: array<int> )
    modifies a;
    ensures multiset(a[..]) == old(multiset(a[..]));
    ensures IsSorted(a,0,a.Length);
{
    var j := 0;
    while j != a.Length
        //
        // a: | í vaxandi röð | óþekkt |
        //     ^               ^        ^
        //     0               j      a.Length
        //
        decreases a.Length-j;
        invariant multiset(a[..]) == old(multiset(a[..]));
        invariant IsSorted(a,0,j);
    {
        var i := j;
        ghost var oldprefix := a[..j];
        j := j+1;
        ghost var oldsuffix := a[j..];
        var x := a[i];
        while( i != 0 && x < a[i-1] )
            //
            // a: |  A   |    B   |  óþekkt   |
            //    |      |x|  C   |           |
            //     ^      ^        ^           ^
            //     0      i        j         a.Length
            //
            // 0 <= i <= j
            // Svæði B (með x=a[i] fremst) er í vaxandi röð
            // Samskeytingin A+C er í vaxandi röð (er reyndar
            // jafnt fyrra raðaða forskeyti).
            invariant 0 <= i < j;
            decreases i;
            invariant multiset(a[..]) == old(multiset(a[..]));
            invariant a[j..] == oldsuffix;
            invariant a[..i]+a[i+1..j] == oldprefix;
            invariant a[i] == x;
            invariant forall p | i+1 <= p < j :: x < a[p];
            invariant IsSorted(a,0,i);
            invariant IsSorted(a,i,j);
        {
            assert i+1 < j ==> x < a[i+1];
            Swap(a,i-1,i);
            i := i-1;
        }
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