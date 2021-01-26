// Höfundur: Snorri Agnarsson, snorri@hi.is

// Útfærsla á merge sort sem er sannanlega 'stable',
// þ.e. viðheldur fyrri röð gildanna að því leyti
// sem mögulegt er.

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

// IsSorted2(a,comp,comp2) er satt þá og því aðeins að sannað
// sé að a sé í vaxandi röð m.v. comp.
predicate IsSorted2<T>( a: seq<T>, comp: (T,T)->int, comp2: (T,T)->int )
    requires IsComparator<T>(comp);
    requires IsComparator<T>(comp2);
{
    (forall p,q | 0 <= p < q < |a| :: comp(a[p],a[q]) <= 0) &&
    (forall p,q | 0 <= p < q < |a| :: comp(a[p],a[q]) == 0 ==> comp2(a[p],a[q]) <= 0)
}

// IsSegmented(a,b,comp) er satt þá og því aðeins að
// sannað sé að öll gildi í a séu <= öll gildi í b.
predicate IsSegmented<T>( a: seq<T> , b: seq<T>, comp: (T,T)->int )
{
    (forall z,w | z in a && w in b :: comp(z,w)<=0) &&
    (forall p,q | 0 <= p < |a| && 0 <= q < |b| :: comp(a[p],b[q])<=0)
}

// IsSegmented2(a,b,comp,comp2) er satt þá og því aðeins að
// sannað sé að öll gildi í a séu <= öll gildi í b, miðað
// við að x<=y sé skilgreint með tveimur samanburðum þar
// sem seinni samanburðurinn, comp2, er notaður fyrir
// gildi sem eru jöfn samkvæmt comp.
predicate IsSegmented2<T>( a: seq<T> , b: seq<T>, comp: (T,T)->int, comp2: (T,T)->int )
{
    (forall z,w | z in a && w in b :: comp(z,w)<=0) &&
    (forall p,q | 0 <= p < |a| && 0 <= q < |b| :: comp(a[p],b[q])<=0) &&
    (forall z,w | z in a && w in b :: comp(z,w)==0 ==> comp2(z,w)<=0) &&
    (forall p,q | 0 <= p < |a| && 0 <= q < |b| :: comp(a[p],b[q])==0 ==> comp2(a[p],b[q])<=0)
}

// Samröðunarfall sem nota má í röksemdafærslu
// en ekki í raunverulegum útreikningum.
function MergeFun<T>( a: seq<T>, b: seq<T>, comp: (T,T)->int ): seq<T>
    decreases |a|+|b|;
{
    if a == [] then
        b
    else if b == [] then
        a
    else if comp(a[0],b[0])<=0 then
        [a[0]]+MergeFun(a[1..],b,comp)
    else
        [b[0]]+MergeFun(a,b[1..],comp)
}

lemma MergeFunWorks<T>( a: seq<T>, b: seq<T>, c: seq<T>, comp: (T,T)->int )
    decreases |a|+|b|;
    requires IsComparator(comp);
    requires IsSorted(a,comp);
    requires IsSorted(b,comp);
    requires c == MergeFun(a,b,comp);
    ensures multiset(c) == multiset(a)+multiset(b);
    ensures IsSorted(c,comp);
    ensures a!=[] && b!=[] && comp(a[0],b[0])<=0 ==> c==a[0..1]+MergeFun(a[1..],b,comp);
    ensures a!=[] && b!=[] && comp(a[0],b[0])>0 ==> c==b[0..1]+MergeFun(a,b[1..],comp);
{
    MergeFunWorks2(a,b,c,comp,(x,y)=>0);
}

// Sannar að MergeFun(a,b,comp) skilar réttu
// gildi og viðheldur fyrri röðun meðal jafnra
// gilda, m.v. að gildi úr a hafi forgang.
// Fyrir mannlega lesendur er það augljóst,
// en Dafny þarf smá hjálp til að sanna það
// með þrepasönnun. Þið munuð vilja kalla á
// þessa hjálparsetningu, eða MergeFunWorks,
// ef þið byggið ykkar samröðun á endurkvæmni.
lemma MergeFunWorks2<T>( a: seq<T>, b: seq<T>, c: seq<T>, comp: (T,T)->int, comp2: (T,T)->int )
    decreases |a|+|b|;
    requires IsComparator(comp);
    requires IsComparator(comp2);
    requires IsSorted2(a,comp,comp2);
    requires IsSorted2(b,comp,comp2);
    requires forall x,y | x in a && y in b :: comp(x,y)==0 ==> comp2(x,y)<=0;
    requires forall p,q | 0 <= p < |a| && 0 <= q < |b| :: comp(a[p],b[q])==0 ==> comp2(a[p],b[q])<=0;
    requires c == MergeFun(a,b,comp);
    ensures multiset(c) == multiset(a)+multiset(b);
    ensures IsSorted2(c,comp,comp2);
    ensures a!=[] && b!=[] && comp(a[0],b[0])<=0 ==> c==a[0..1]+MergeFun(a[1..],b,comp);
    ensures a!=[] && b!=[] && comp(a[0],b[0])>0 ==> c==b[0..1]+MergeFun(a,b[1..],comp);
{
    if a == [] || b == [] { return; }
    if comp(a[0],b[0])<=0
    {
        MergeFunWorks2(a[1..],b,c[1..],comp,comp2);
        assert comp(a[0],c[1])<=0;
        calc ==
        {
            multiset(c);
            multiset(c[0..1]+c[1..]);
            multiset(c[0..1])+multiset(c[1..]);
            multiset(c[0..1])+multiset(a[1..])+multiset(b);
            assert c[0]==a[0];
            assert a == c[0..1]+a[1..];
            assert multiset(c[0..1])+multiset(a[1..]) == multiset(a);
            multiset(a[0..1])+multiset(a[1..])+multiset(b);
            multiset(a[0..1]+a[1..])+multiset(b);
            assert a[0..1]+a[1..] == a;
            multiset(a)+multiset(b);
        }
    }
    else
    {
        MergeFunWorks2(a,b[1..],c[1..],comp,comp2);
        assert comp(b[0],c[1])<=0;
        calc ==
        {
            multiset(c);
            multiset(c[0..1]+c[1..]);
            multiset(c[0..1])+multiset(c[1..]);
            multiset(c[0..1])+multiset(a)+multiset(b[1..]);
            assert c[0]==b[0];
            multiset(b[0..1])+multiset(a)+multiset(b[1..]);
            multiset(a)+multiset(b[0..1])+multiset(b[1..]);
            multiset(a)+multiset(b[0..1]+b[1..]);
            assert b[0..1]+b[1..] == b;
            multiset(a)+multiset(b);
        }
    }
}

method Merge2<T>( a: seq<T>
                , b: seq<T>
                , comp: (T,T)->int
                , ghost comp2: (T,T)->int
                ) returns ( c: seq<T> )
    decreases |a|+|b|;
    requires IsComparator(comp);
    requires IsComparator(comp2);
    requires IsSorted2(a,comp,comp2);
    requires IsSorted2(b,comp,comp2);
    requires forall x,y | x in a && y in b :: comp2(x,y)<=0;
    requires forall p,q | 0 <= p < |a| && 0 <= q < |b| :: comp2(a[p],b[q])<=0;
    ensures c == MergeFun(a,b,comp);
    ensures multiset(c) == multiset(a)+multiset(b);
    ensures IsSorted2(c,comp,comp2);
    ensures a!=[] ==> a==a[0..1]+a[1..];
    ensures b!=[] ==> b==b[0..1]+b[1..];
{
    if a == []
    {
        ghost var c' := MergeFun(a,b,comp);
        assert a == [];
        assert !exists z :: z in a;
        assert forall z | z in a :: false;
        assert forall x,y | x in a && y in b :: comp2(x,y)<=0;
        MergeFunWorks2(a,b,c',comp,comp2);
        assert c' == b;
        return b;
    }
    if b == []
    {
        ghost var c' := MergeFun(a,b,comp);
        assert !exists z :: z in b;
        assert forall z | z in b :: false;
        assert forall x,y | x in a && y in b :: comp2(x,y)<=0;
        MergeFunWorks2(a,b,c',comp,comp2);
        assert c' == a;
        return a;
    }
    if comp(a[0],b[0]) <= 0
    {
        ghost var c' := MergeFun(a,b,comp);
        ghost var c'' := MergeFun(a[1..],b,comp);
        MergeFunWorks2(a,b,c',comp,comp2);
        MergeFunWorks2(a[1..],b,c'',comp,comp2);
        assert c'' == c'[1..];
        assert c'[0] == a[0];
        c := Merge2(a[1..],b,comp,comp2);
        assert c == c'';
        assert comp(a[0],c[0])<=0;
        assert comp(a[0],c[0])==0 ==> comp2(a[0],c[0])<=0;
        c := a[0..1]+c;
        assert c == c';
    }
    else
    {
        ghost var c' := MergeFun(a,b,comp);
        ghost var c'' := MergeFun(a,b[1..],comp);
        MergeFunWorks2(a,b,c',comp,comp2);
        MergeFunWorks2(a,b[1..],c'',comp,comp2);
        assert c'' == c'[1..];
        assert c'[0] == b[0];
        c := Merge2(a,b[1..],comp,comp2);
        assert c == c'';
        assert comp(b[0],c[0])<=0;
        assert comp(b[0],c[0])==0 ==> comp2(b[0],c[0])<=0;
        c := b[0..1]+c;
        assert c == c';
    }
}

method Merge<T> ( a: seq<T>
                , b: seq<T>
                , comp: (T,T)->int
                ) returns ( c: seq<T> )
    decreases |a|+|b|;
    requires IsComparator(comp);
    requires IsSorted(a,comp);
    requires IsSorted(b,comp);
    ensures c == MergeFun(a,b,comp);
    ensures multiset(c) == multiset(a)+multiset(b);
    ensures IsSorted(c,comp);
    ensures a!=[] ==> a==a[0..1]+a[1..];
    ensures b!=[] ==> b==b[0..1]+b[1..];
{
    if a == [] { return b; }
    if b == [] { return a; }
    ghost var c' := MergeFun(a,b,comp);
    MergeFunWorks(a,b,c',comp);
    if comp(a[0],b[0]) <= 0
    {
        c := Merge(a[1..],b,comp);
        MergeFunWorks(a[1..],b,c,comp);
        assert c == c'[1..];
        c := a[0..1]+c;
    }
    else
    {
        c := Merge(a,b[1..],comp);
        MergeFunWorks(a,b[1..],c,comp);
        assert c == c'[1..];
        c := b[0..1]+c;
    }
}

// Sannar að Sort2 fallið virkar, séu forsendur fyrir hendi.
lemma SortWorks2<T> ( a: seq<T>
                    , c: seq<T>
                    , d: seq<T>
                    , c': seq<T>
                    , d': seq<T>
                    , comp: (T,T)->int
                    , comp2: (T,T)->int
                    )
    requires a == c+d;
    requires IsComparator(comp);
    requires IsComparator(comp2);
    requires multiset(c') == multiset(c);
    requires multiset(d') == multiset(d);
    requires IsSorted(a,comp2);
    requires IsSorted2(c',comp,comp2);
    requires IsSorted2(d',comp,comp2);
    requires forall x,y | x in c && y in d :: comp2(x,y)<=0;
    ensures forall x,y | x in c' && y in d' :: comp2(x,y)<=0;
    ensures multiset(a) == multiset(MergeFun(c',d',comp));
    ensures IsSorted2(MergeFun(c',d',comp),comp,comp2);
{
    assert forall x | x in c' :: x in multiset(c') && x in multiset(c) && x in c;
    assert forall x | x in d' :: x in multiset(d') && x in multiset(d) && x in d;
    assert forall x,y | x in c' && y in d' :: comp2(x,y)<=0;
    MergeFunWorks2(c',d',MergeFun(c',d',comp),comp,comp2);
}   

method Sort2<T>( a: seq<T>, comp: (T,T)->int, ghost comp2: (T,T)->int ) returns ( b: seq<T> )
    decreases |a|;
    requires IsComparator(comp);
    requires IsComparator(comp2);
    requires IsSorted(a,comp2);
    ensures IsSorted2(b,comp,comp2);
    ensures multiset(a) == multiset(b);
{
    if |a| < 2 { return a; }
    var c := Sort2(a[..|a|/2],comp,comp2);
    var d := Sort2(a[|a|/2..],comp,comp2);
    SortWorks2(a,a[..|a|/2],a[|a|/2..],c,d,comp,comp2);
    b := Merge2(c,d,comp,comp2);
}

lemma SortWorks<T>  ( a: seq<T>
                    , c: seq<T>
                    , d: seq<T>
                    , c': seq<T>
                    , d': seq<T>
                    , comp: (T,T)->int
                    )
    requires a == c+d;
    requires IsComparator(comp);
    requires multiset(c') == multiset(c);
    requires multiset(d') == multiset(d);
    requires IsSorted(c',comp);
    requires IsSorted(d',comp);
    ensures multiset(a) == multiset(MergeFun(c',d',comp));
    ensures IsSorted(MergeFun(c',d',comp),comp);
{
    MergeFunWorks(c',d',MergeFun(c',d',comp),comp);
}   

method Sort<T>( a: seq<T>, comp: (T,T)->int ) returns ( b: seq<T> )
    decreases |a|;
    requires IsComparator(comp);
    ensures IsSorted(b,comp);
    ensures multiset(a) == multiset(b);
{
    if |a| < 2 { return a; }
    var m := |a|/2;
    var c := Sort(a[..m],comp);
    var d := Sort(a[m..],comp);
    SortWorks(a,a[..m],a[m..],c,d,comp);
    b := Merge(c,d,comp);
}

method Test( a: seq<int> ) returns ( b: seq<int> )
    ensures multiset(a) == multiset(b);
    ensures IsSorted(b,(x,y)=>x-y);
    ensures forall p,q | 0 <= p < q < |b| :: b[p]<=b[q];
{
    b := Sort(a,(x,y)=>(x%10)-(y%10));
    b := Sort2(b,(x,y)=>(x/10)-(y/10),(x,y)=>(x%10)-(y%10));
}

// Aðalforritið er óþarfi, en er sett hér til gamans
// svo hægt sé að keyra eitthvað.
method Main()
{
    var x := Test([1,902,103,804,205,706,307,608,409,510,11,912,113,814,215,716,317,618,419,520]);
    print x;
    print "\n";
    x := Sort(x,(a,b)=>b%10-a%10);
    print x;
}