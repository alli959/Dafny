
// Quicksort fyrir seq<int>.

// Höfundur:  Snorri Agnarsson, snorri@hi.is

// IsComparator(c) er satt þá og því aðeins að sannað
// sé að c sé nothæft sem samanburðarfall.
predicate IsComparator<T(!new)>( c: (T,T)->int )
{
    (forall x :: c(x,x) == 0) &&
    (forall x,y,z :: c(x,y)<=0 && c(y,z)<=0 ==> c(x,z)<=0) &&
    (forall x,y :: c(x,y) == -c(y,x))
}

// IsSorted(a,comp) er satt þá og því aðeins að sannað
// sé að a sé í vaxandi röð m.v. comp.
predicate IsSorted<T>( a: seq<T>, comp: (T,T)->int )
    requires IsComparator<T>(comp);
{
    forall p,q | 0 <= p < q < |a| :: comp(a[p],a[q]) <= 0
}

lemma QuicksortWorks<T>
        ( s: multiset<T>
        , a0: multiset<T>
        , c0: multiset<T>
        , a: seq<T>
        , b: seq<T>
        , c: seq<T>
        , piv: T
        , comp: (T,T)->int
        )
    requires IsComparator(comp);
    requires IsSorted(a,comp);
    requires IsSorted(c,comp);
    requires s == a0+multiset(b)+c0;
    requires a0 == multiset(a);
    requires c0 == multiset(c);
    requires forall z | z in a0 :: comp(z,piv) <= 0;
    requires forall z | z in b :: comp(z,piv) == 0;
    requires forall z | z in c0 :: comp(z,piv) >= 0;
    ensures multiset(a+b+c) == s;
    ensures IsSorted(a+b+c,comp);
{
    var r := a+b+c;
    assert forall z | z in a ::
        z in multiset(a) &&
        z in a0;
    assert forall z | z in c ::
        z in multiset(c) &&
        z in c0;
    assert forall t | 0 <= t < |a| ::
        r[t] == a[t] &&
        r[t] in a &&
        r[t] in a0 &&
        comp(r[t],piv) <= 0 &&
        comp(piv,r[t]) >= 0;
    assert forall t | |a| <= t < |a+b| ::
        r[t] == b[t-|a|] &&
        r[t] in b &&
        comp(r[t],piv) == 0 &&
        comp(piv,r[t]) == 0;
    assert forall t | |a+b| <= t < |r| ::
        r[t] == c[t-|a+b|] &&
        r[t] in c &&
        r[t] in c0 &&
        comp(r[t],piv) >= 0 &&
        comp(piv,r[t]) <= 0;
    // x,y in a
    assert forall p,q | 0 <= p < q < |a| ::
        r[p] == a[p] &&
        r[q] == a[q] &&
        comp(r[p],r[q]) <= 0;
    // x in a, y in b
    assert forall p,q | 0 <= p < |a| && |a| <= q < |a+b| ::
        r[p] in a &&
        r[q] in b &&
        comp(r[p],piv) <= 0 &&
        comp(piv,r[q]) == 0 &&
        comp(r[p],r[q]) <= 0;
    // x in a, y in c
    assert forall p,q | 0 <= p < |a| <= |a+b| <= q < |r| ::
        r[p] == a[p] &&
        r[q] == c[q-|a+b|] &&
        r[p] in a &&
        r[q] in c &&
        comp(r[p],piv) <= 0 &&
        comp(r[q],piv) >= 0 &&
        comp(piv,r[q]) <= 0 &&
        comp(r[p],r[q]) <= 0;
    // a,y in b
    assert forall p,q | |a| <= p < q < |a+b| ::
        r[p] in b &&
        r[q] in b &&
        comp(r[p],r[q]) == 0;
    // x in b, y in c
    assert forall p,q | |a| <= p < |a+b| <= q < |r| ::
        r[p] in b &&
        r[q] in c &&
        comp(r[p],r[q]) <= 0;
    // x,y in c
    assert forall p,q | |a+b| <= p < q < |r| ::
        comp(r[p],r[q]) <= 0;
}

method DijkstraPartition<T>( s: seq<T>, comp: (T,T)->int )
        returns ( a: seq<T>, b: seq<T>, c: seq<T> )
    requires IsComparator(comp);
    requires |s| >= 1;
    ensures multiset(s) == multiset(a)+multiset(b)+multiset(c);
    ensures |b| > 0;
    ensures forall x,y | x in a && y in b :: comp(x,y) < 0;
    ensures forall x,y | x in b && y in b :: comp(x,y) == 0;
    ensures forall x,y | x in b && y in c :: comp(x,y) < 0;
    ensures forall x,y | x in a && y in c :: comp(x,y) < 0;
    ensures |a| == |multiset(a)| < |multiset(s)| == |s|;
    ensures |c| == |multiset(c)| < |multiset(s)| == |s|;
{
    var rest := s;
    var p := rest[0];
    rest := rest[1..];
    a := [];
    b := [p];
    c := [];
    assert s == b+rest;
    while rest != []
        decreases |rest|;
        invariant |b| > 0;
        invariant multiset(s) == multiset(rest)+multiset(a)+multiset(b)+multiset(c);
        invariant forall x | x in a :: comp(x,p) < 0;
        invariant forall x | x in b :: comp(x,p) == 0;
        invariant forall x | x in c :: comp(x,p) > 0;
    {
        assert rest == rest[0..1]+rest[1..];
        if comp(rest[0],p) < 0       { a := a+rest[0..1]; }
        else if comp(rest[0],p) == 0 { b := b+rest[0..1]; }
        else                         { c := c+rest[0..1]; }
        rest := rest[1..];
    }
}

method Sort<T>( s: seq<T>, comp: (T,T)->int ) returns ( r: seq<T> )
    decreases |s|;
    requires IsComparator(comp)
    ensures multiset(s) == multiset(r);
    ensures IsSorted(r,comp);
{
    if |s| == 0 { return []; }
    var a,b,c := DijkstraPartition(s,comp);
    var a' := Sort(a,comp);
    var c' := Sort(c,comp);
    r := a'+b+c';
    QuicksortWorks(multiset(s),multiset(a),multiset(c),a',b,c',b[0],comp);
}

method Test( m: seq<int> ) 
{
    var s := Sort(m,(x,y)=>x-y);
    print s;
    assert IsSorted(s,(x,y)=>x-y);
    assert multiset(m) == multiset(s);
    if |m| > 0
    {
        var a,b,c := DijkstraPartition(m,(x,y)=>x-y);
        assert multiset(m) == multiset(a)+multiset(b)+multiset(c);
        var p := b[0];
        assert p in b;
        assert forall x | x in a :: x < p;
        assert forall x | x in b :: x == p;
        assert forall x | x in c :: x > p;
    }
}

method Main()
{
    Test([9,1,8,2,7,3,6,4,5]);
}