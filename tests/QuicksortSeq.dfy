// Quicksort fyrir seq<int>.

// Höfundur:  Snorri Agnarsson, snorri@hi.is

// IsSorted(a) er satt þá og því aðeins að sannað
// sé að a er í vaxandi röð.
predicate IsSorted( a: seq<int> )
{
    forall p,q | 0<=p<q<|a| :: a[p]<=a[q]
}

// Notkun: var b,p,c := Partition(a);
// Fyrir:  a er runa heiltalna, ekki tóm.
// Eftir:  b og c eru runur og p er heiltala þannig
//         að samanlagt innihalda þessar þrjár breytur
//         öll gildin úr a. Öll gildi í b eru <=p, öll
//         gildi í c eru >=p.
method Partition( a: seq<int> ) returns ( b: seq<int>, p: int, c: seq<int> )
    requires |a| >= 1;
    ensures multiset(a) == multiset(b)+multiset{p}+multiset(c);
    ensures forall z | z in b :: z<=p;
    ensures forall z | z in c :: z>=p;
    ensures |b|==|multiset(b)|<|multiset(a)|==|a|;
    ensures |c|==|multiset(c)|<|multiset(a)|==|a|;
{
    var rest := a;
    p := rest[0];
    rest := rest[1..];
    assert a == [p]+rest;
    b := [];
    c := [];
    while |rest| != 0
        decreases rest;
        invariant multiset(a) == multiset(rest)+multiset(b)+multiset{p}+multiset(c);
        invariant forall z | z in b :: z<=p;
        invariant forall z | z in c :: z>=p;
    {
        assert rest == rest[0..1]+rest[1..];
        if rest[0] <= p { b := b+rest[0..1]; }
        else            { c := c+rest[0..1]; }
        rest := rest[1..];
    }
}

// Hjálparsetning til að hjálpa að sanna að
// útkoman úr röðuninni sé rétt.
lemma LomutoLemma   ( a: seq<int>
                    , a': seq<int>
                    , x: int
                    , b: seq<int>
                    , b': seq<int>
                    , c: seq<int> 
                    )
    requires multiset(a) == multiset(a');
    requires multiset(b) == multiset(b');
    requires IsSorted(a');
    requires IsSorted(b');
    requires forall z | z in a :: z<=x;
    requires forall z | z in b :: z>=x;
    requires c == a'+[x]+b';
    ensures forall p | 0<=p<|a'| :: a'[p] in multiset(a') && a'[p] in multiset(a) && a'[p] in a;
    ensures forall p | 0<=p<|b'| :: b'[p] in multiset(b') && b'[p] in multiset(b) && b'[p] in b;
    ensures forall z | z in a :: z in multiset(a) && z in multiset(a') && z in a';
    ensures forall z | z in b :: z in multiset(b) && z in multiset(b') && z in b';
    ensures forall z | z in a' :: z in a && z<=x;
    ensures forall z | z in b' :: z in b && z>=x;
    ensures forall z | z in a' :: z in a && z<=x;
    ensures forall z | z in b' :: z in b && z>=x;
    ensures IsSorted(c);
    ensures multiset(c) == multiset(a)+multiset{x}+multiset(b);
{
    assert |c| == |a'|+1+|b'|;
    assert forall p,q | 0<=p<q<|c| :: q<|a'| ==> c[p]<=c[q];
    assert forall p,q | 0<=p<q<|c| :: q==|a'| ==> 
        c[q]==x && 
        p<|a'| && 
        c[p]==a'[p] && 
        c[p] in a' && 
        c[p] in multiset(a') &&
        c[p] in multiset(a) &&
        c[p] in a && 
        c[p]<=c[q];
    assert forall p,q | 0<=p<q<|c| :: p<|a'| && q>|a'| ==> 
        c[p] in a' && 
        c[p] in multiset(a') &&
        c[p] in multiset(a) &&
        c[p] in a &&
        c[q] in b' && 
        c[q] in multiset(b') &&
        c[q] in multiset(b) &&
        c[q] in b;
    assert forall p,q | 0<=p<q<|c| :: p==|a'| && q>|a'| ==> 
        c[p]==x && 
        c[q] in b' && 
        c[q] in multiset(b') &&
        c[q] in multiset(b) &&
        c[q] in b && 
        x<=c[q] && 
        c[p]<=c[q];
    assert forall p,q | 0<=p<q<|c| :: p>|a'| && q>|a'| ==> c[p]<=c[q];
}

method Sort( s: seq<int> ) returns ( r: seq<int> )
    decreases |s|;
    ensures multiset(s) == multiset(r);
    ensures IsSorted(r);
{
    if |s| == 0 { return []; }
    var b,p,c := Partition(s);
    var b' := Sort(b);
    var c' := Sort(c);
    r := b'+[p]+c';
    LomutoLemma(b,b',p,c,c',r);
}

method Test( m: seq<int> )
{
    var s := Sort(m);
    assert IsSorted(s);
    assert multiset(m) == multiset(s);
    if |m| > 0
    {
        var a,p,b := Partition(m);
        assert multiset(m) == multiset(a)+multiset{p}+multiset(b);
        assert forall z | z in a :: z<=p;
        assert forall z | z in b :: z>=p;
    }
}