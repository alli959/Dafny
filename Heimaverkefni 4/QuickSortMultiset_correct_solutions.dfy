// Höfundur: Snorri Agnarsson, snorri@hi.is

// IsSorted(a) er satt þá og því aðeins að sannað
// sé að a sé í vaxandi röð.
predicate IsSorted( a: seq<int> )
{
    forall p,q | 0 <= p < q < |a| :: a[p] <= a[q]
}

// IsSegmented(a,b) er satt þá og því aðeins að
// sannað sé að öll gildi í a séu <= öll gildi í b.
predicate IsSegmented( a: seq<int> , b: seq<int> )
{
    (forall z,w | z in a && w in b :: z <= w) &&
    (forall p,q | 0 <= p < |a| && 0 <= q < |b| :: a[p] <= b[q])
}

// SortedEquals(a,b) sannar, fyrir raðaðar runur
// a og b, sem innihalda sama poka gilda, að runurnar
// eru jafnar.
lemma SortedEquals( a: seq<int>, b: seq<int> )
    requires multiset(a) == multiset(b);
    requires IsSorted(a);
    requires IsSorted(b);
    ensures a == b;
{
    if a == []
    {
        assert |b| == 0 || b[0] in multiset(a);
        return;
    }
    if b == []
    {
        assert |a| == 0 || a[0] in multiset(b);
        return;
    }
    assert a[0] in multiset(b);
    assert b[0] in multiset(a);
    assert a == a[0..1]+a[1..];
    assert b == b[0..1]+b[1..];
    assert a[0] == b[0];
    assert multiset(a[1..]) == multiset(a)-multiset{a[0]};
    assert multiset(b[1..]) == multiset(b)-multiset{b[0]};
    SortedEquals(a[1..],b[1..]);
}

// Samröðunarfall sem nota má í röksemdafærslu
// en ekki í raunverulegum útreikningum.
function MergeFun( a: seq<int>, b: seq<int> ): seq<int>
    decreases |a|+|b|;
{
    if a == [] then
        b
    else if b == [] then
        a
    else if a[0] <= b[0] then
        [a[0]]+MergeFun(a[1..],b)
    else
        [b[0]]+MergeFun(a,b[1..])
}

// Sannar að MergeFun(a,b) skilar réttu gildi.
// Fyrir mannlega lesendur er það augljóst,
// en Dafny þarf smá hjálp til að sanna það
// með þrepasönnun. Þið munuð vilja kalla á
// þessa hjálparsetningu ef þið byggið ykkar
// samröðun á endurkvæmni.
lemma MergeFunWorks( a: seq<int>, b: seq<int>, c: seq<int> )
    decreases |a|+|b|;
    requires IsSorted(a);
    requires IsSorted(b);
    requires c == MergeFun(a,b);
    ensures multiset(c) == multiset(a)+multiset(b);
    ensures IsSorted(c);
    ensures a!=[] && b!=[] && a[0]<=b[0] ==> c==a[0..1]+MergeFun(a[1..],b);
    ensures a!=[] && b!=[] && a[0]>=b[0] ==> c==b[0..1]+MergeFun(a,b[1..]);
{
    if a == [] || b == [] { return; }
    if a[0] <= b[0]
    {
        MergeFunWorks(a[1..],b,c[1..]);
        calc ==
        {
            multiset(c);
            multiset(c[0..1]+c[1..]);
            multiset(c[0..1])+multiset(c[1..]);
            multiset(c[0..1])+multiset(a[1..])+multiset(b);
            multiset(a[0..1])+multiset(a[1..])+multiset(b);
            multiset(a[0..1]+a[1..])+multiset(b);
            assert a[0..1]+a[1..] == a;
            multiset(a)+multiset(b);
        }
    }
    else
    {
        MergeFunWorks(a,b[1..],c[1..]);
        calc ==
        {
            multiset(c);
            multiset(c[0..1]+c[1..]);
            multiset(c[0..1])+multiset(c[1..]);
            multiset(c[0..1])+multiset(a)+multiset(b[1..]);
            multiset(b[0..1])+multiset(a)+multiset(b[1..]);
            multiset(a)+multiset(b[0..1])+multiset(b[1..]);
            multiset(a)+multiset(b[0..1]+b[1..]);
            assert b[0..1]+b[1..] == b;
            multiset(a)+multiset(b);
        }
    }
}

// Sannar að poki með einu staki samsvarar runu
// með einu staki.  Dafny þarf smávegis olnbogaskot
// til að fatta það. Þetta er gagnlegt til að sanna
// að útkoman úr Sort sé rétt í sértilvikinu þegar
// raðað er poka m með aðeins einu gildi x, sem
// gefur þá rununa s == [x].
lemma Singleton( m: multiset<int>, s: seq<int>, x: int )
    requires x in m;
    requires x in s;
    requires |s| == 1 == |m|;
    ensures |m-multiset{x}| == 0;
    ensures s == [x];
    ensures m == multiset{x};
    ensures m == multiset(s);
    ensures IsSorted(s);
{}

// Raðar innihaldi poka yfir í runu með mergesort.
method Sort( a: multiset<int> ) returns ( b: seq<int> )
    decreases |a|;
    ensures a == multiset(b);
    ensures IsSorted(b);
{
    if |a| == 0 { return []; }
    if |a| == 1
    {
        var x :| x in a;
        Singleton(a,[x],x);
        return [x];
    }
    var c, d := Split(a);
    var e := Sort(c);
    var f := Sort(d);
    b := MergeLoop(e,f);
}

// Skiptir innihaldi poka í tvennt þannig að pokarnir
// sem koma út eru nokkurn veginn jafn stórir.
method Split( a: multiset<int> )
        returns ( b: multiset<int>
                , c: multiset<int>
                )
    decreases a;
    ensures a == b+c;
    ensures |b| == |c| || |b| == |c|+1;
{
    if |a| < 2
    {
        b := a;
        c := multiset{};
        return;
    }
    var rest,x,y := RemoveTwo(a);
    b, c := Split(rest);
    b := b+multiset{x};
    c := c+multiset{y};
}

method MergeLoop( a: seq<int>, b: seq<int> ) returns( c: seq<int> )
    requires IsSorted(a);
    requires IsSorted(b);
    ensures IsSorted(c);
    ensures multiset(a)+multiset(b) == multiset(c);
    ensures c == MergeFun(a,b);
{
    c := [];
    var a' := a;
    var b' := b;
    while a' != [] && b' != []
        decreases |a'|+|b'|;
        invariant multiset(a)+multiset(b) == multiset(c)+multiset(a')+multiset(b');
        invariant IsSegmented(c,a');
        invariant IsSegmented(c,b');
        invariant IsSorted(a');
        invariant IsSorted(b');
        invariant IsSorted(c);
    {
        assert a' == a'[0..1]+a'[1..];
        assert b' == b'[0..1]+b'[1..];
        if a'[0] <= b'[0]
        {
            c := c+a'[0..1];
            a' := a'[1..];
        }
        else
        {
            c := c+b'[0..1];
            b' := b'[1..];
        }
    }
    c := c+a'+b';
    MergeFunWorks(a,b,MergeFun(a,b));
    SortedEquals(c,MergeFun(a,b));
}

method MergeRecursive( a: seq<int>, b: seq<int> ) returns( c: seq<int> )
    requires IsSorted(a);
    requires IsSorted(b);
    ensures IsSorted(c);
    ensures multiset(a)+multiset(b) == multiset(c);
    ensures c == MergeFun(a,b);
{
    if a == [] { return b; }
    if b == [] { return a; }
    if a[0] <= b[0]
    {
        c := MergeRecursive(a[1..],b);
        c := a[0..1]+c;
        MergeFunWorks(a,b,c);
    }
    else
    {
        c := MergeRecursive(a,b[1..]);
        c := b[0..1]+c;
        MergeFunWorks(a,b,c);
    }
}

// Fjarlægir tvö gildi úr poka.
// Notkun: var b,x,y := RemoveTwo(a);
// Fyrir:  pokinn a inniheldur a.m.k. tvö gildi.
// Eftir:  a == b+multiset{x,y}
method RemoveTwo( a: multiset<int> ) returns( b: multiset<int>, x: int, y: int )
    requires |a| >= 2;
    ensures a == b+multiset{x,y};
{
    b := a;
    x :| x in b;
    b := b-multiset{x};
    assert |b| >= 1;
    y :| y in b;
    b := b-multiset{y};
}

// Skiptir innihaldi poka í tvennt þannig að pokarnir
// sem koma út eru nokkurn veginn jafn stórir.
method SplitLoop( a: multiset<int> )
        returns ( b: multiset<int>
                , c: multiset<int>
                )
    ensures a == b+c;
    ensures |b| == |c| || |b| == |c|+1;
{
    var rest := a;
    var x,y : int;
    b := multiset{};
    c := multiset{};
    while |rest| >= 2
        decreases rest;
        invariant a == rest+b+c;
        invariant |b| == |c|;
    {
        rest, x, y := RemoveTwo(rest);
        b := b+multiset{x};
        c := c+multiset{y};
    }
    b := b+rest;
}

// Prófunarfall sem staðfestir að Split og Sort
// séu áreiðanlega að virka sannanlega rétt.
method Test( x: multiset<int> )
{
    var a,b := Split(x);
    assert a+b == x;
    assert (|a|==|b|) || (|a|==|b|+1);
    a,b := SplitLoop(x);
    assert a+b == x;
    assert (|a|==|b|) || (|a|==|b|+1);
    var c := Sort(x);
    assert multiset(c) == x;
    assert IsSorted(c);
}

// Aðalforritið er óþarfi, en er sett hér til gamans
// svo hægt sé að keyra eitthvað.
method Main()
{
    var x := Sort(multiset{0,9,1,8,2,7,3,6,4,5
                          ,0,9,1,8,2,7,3,6,4,5
                          }
                 );
    print x;    
}