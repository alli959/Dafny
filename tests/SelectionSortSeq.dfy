// Selection sort.
//
// Author: Snorri Agnarsson, snorri@hi.is

predicate IsSorted( s: seq<int> )
{
    forall p,q | 0 <= p < q < |s| :: s[p] <= s[q]
}

lemma SelectionLemma( a: seq<int>, x: int, a': seq<int>, b: seq<int>, k: int, b': seq<int> )
    requires IsSorted(a);
    requires 0 <= k < |b|;
    requires x == b[k];
    requires forall z,w | z in a && w in b :: z <= w;
    requires forall w | w in b :: x <= w;
    requires forall w | w in a :: x in b && w <= x;
    requires a' == a+[x];
    requires b' == b[..k]+b[k+1..];
    ensures IsSorted(a');
    ensures multiset(a')+multiset(b') == multiset(a)+multiset(b);
{
    assert forall p | 0<=p<|a| :: a[p] in a;
    assert x in b;
    assert forall p | 0<=p<|a| :: a[p] in a && a[p]<=x;
    calc ==
    {
        multiset(b[..k])+multiset(b[k..k+1]);
        multiset(b[..k]+b[k..k+1]);
        assert b[..k]+b[k..k+1] == b[..k+1];
        multiset(b[..k+1]);
    }
    calc ==
    {
        multiset(b');
        multiset(b[..k]+b[k+1..]);
        multiset(b[..k])+multiset(b[k+1..]);
        multiset(b[..k])+multiset(b[k+1..])+multiset{x}-multiset{x};
        multiset(b[..k])+multiset{x}+multiset(b[k+1..])-multiset{x};
        multiset(b[..k])+multiset{b[k]}+multiset(b[k+1..])-multiset{x};
        multiset(b[..k])+multiset(b[k..k+1])+multiset(b[k+1..])-multiset{x};
        multiset(b[..k]+b[k..k+1])+multiset(b[k+1..])-multiset{x};
        multiset(b[..k+1])+multiset(b[k+1..])-multiset{x};
        multiset(b[..k+1]+b[k+1..])-multiset{x};
        assert b[..k+1]+b[k+1..] == b;
        multiset(b)-multiset{x};
    }
    calc ==
    {
        multiset(a')+multiset(b');
        multiset(a)+multiset{x}+multiset(b');
        multiset(a)+multiset{x}+multiset(b)-multiset{x};
        multiset(a)+multiset(b);
    }
}

method SelectionSort( s: seq<int> ) returns ( r: seq<int> )
    ensures multiset(r) == multiset(s);
    ensures IsSorted(r);
{
    r := [];
    var rest := s;
    while rest != []
        // r inniheldur minnstu gildin í vaxandi röð,
        // rest inniheldur stærstu gildin í óskilgreindri röð.
        decreases |rest|;
        invariant multiset(s) == multiset(r)+multiset(rest);
        invariant forall x,y | x in r && y in rest :: x <= y;
        invariant IsSorted(r);
    {
        var k := 0;
        var i := 1;
        while i < |rest|
            // rest[k] er minnsta gildið í rest[0..i].
            decreases |rest|-i;
            invariant 0 <= k < i <= |rest|;
            invariant forall p | 0 <= p < i :: rest[p] >= rest[k];
        {
            if rest[i] < rest[k] { k := i; }
            i := i+1;
        }
        var x := rest[k];
        SelectionLemma(r,x,r+[x],rest,k,rest[..k]+rest[k+1..]);
        r := r+[x];
        rest := rest[..k]+rest[k+1..];
    }
}