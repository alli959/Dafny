
// IsComparator(c) er satt þá og því aðeins að sannað
// sé að c sé nothæft sem samanburðarfall.
predicate IsComparator<T(!new)>( c: (T,T)->int )
{
    (forall x :: c(x,x) == 0) &&
    (forall x,y,z :: c(x,y) <= 0 && c(y,z) <= 0 ==> c(x,z) <= 0) &&
    (forall x,y :: c(x,y) == -c(y,x))
}

// IsSorted(a,comp) er satt þá og því aðeins að sannað
// sé að a sé í vaxandi röð m.v. comp.
predicate IsSorted<T>( a: seq<T>, comp: (T,T)->int )
    requires IsComparator<T>(comp);
{
    forall p,q | 0 <= p < q < |a| :: comp(a[p],a[q]) <= 0
}

// Skiptingaraðferð Lomutos fyrir quicksort
method PartitionLomuto<T>( a: array<T>, i: int, j: int, comp: (T,T)->int ) returns( r: int )
    modifies a;
    requires IsComparator(comp);
    requires 0 <= i < j <= a.Length;
    ensures i <= r < j;
    ensures a[..i] == old(a[..i]);
    ensures a[j..] == old(a[j..]);
    ensures multiset(a[i..j]) == old(multiset(a[i..j]));
    ensures forall t | i <= t < r :: comp(a[t],a[r]) < 0;
    ensures forall t | r < t < j :: comp(a[t],a[r]) >= 0;
{
    ghost var a0 := a[..];
    var p := a[i];
    r := i+1;
    var s := r;
    while s != j
        // |p| <p | >=p | ??? |
        //  i      r     s     j
        decreases j-s;
        invariant i < r <= s <= j;
        invariant a[i] == p;
        invariant a[..i] == old(a[..i]);
        invariant a[j..] == old(a[j..]);
        invariant multiset(a[i..j]) == old(multiset(a[i..j]));
        invariant forall t | i < t < r :: comp(a[t],p) < 0;
        invariant forall t | r <= t < s :: comp(a[t],p) >= 0;
    {
        if comp(a[s],p) < 0 
        {
            if r != s
            {
                ghost var a' := a[..];
                Swap(a,r,s);
                // a': |p| <p | >=p |x| ??? |   x<p
                // a:  |p| <p |x| >=p | ??? |
                //      i      r     s       j
                SwappingLemmaLoop(a',a[..],i,r,s,j,p,comp);
            }
            r := r+1;
        }
        s := s+1;
    }
    ghost var a1 := a[..];
    // |p| <p | >=p |
    //  i      r     j
    r := r-1;
    // |p| <p | >=p |
    //  i    r       j
    if i == r
    {
        // |p| >=p |
        //  i       j
        //  r
        return;
    }
    ghost var a' := a[..];
    // |p| <p | >=p |
    //  i    r       j
    Swap(a,i,r);
    // | <p |p| >=p |
    //  i    r       j
    SwappingLemmaFinal(a',a[..],i,r,j,p,comp);
}

// Quicksort með skiptingaraðferð Lomutos
method LomutoSort<T>( a: array<T>, i: int, j: int, comp: (T,T)->int )
    decreases j-i;
    requires IsComparator(comp);
    requires 0 <= i <= j <= a.Length;
    modifies a;
    ensures a[..i] == old(a[..i]);
    ensures a[j..] == old(a[j..]);
    ensures multiset(a[i..j]) == old(multiset(a[i..j]));
    ensures IsSorted(a[i..j],comp);
{
    if j-i < 2 { return; }
    ghost var a0 := a[..];
    var r := PartitionLomuto(a,i,j,comp);
    // | <p |p| >=p |
    //  i    r       j
    ghost var p := a[r];
    ghost var a1 := a[..];
    LomutoSort(a,i,r,comp);
    ghost var a2 := a[..];
    LomutoSort(a,r+1,j,comp);
    ghost var a3 := a[..];
    QuicksortPermutes(a0,a1,a2,a3,i,r,r+1,j,p,comp);
    QuicksortSorts(a0,a1,a2,a3,i,r,r+1,j,p,comp);
}

// Sanna að ef tvær runur eru jafnar þá eru samsvarandi
// undirrunur í rununum einnig jafnar.
lemma SubSeqEQ<T>( a: seq<T>, b: seq<T>, i: int, j: int, k: int )
    decreases j-i;
    requires 0 <= i <= j <= k <= |a| == |b|
    requires a[i..k] == b[i..k];
    ensures a[i..j] == b[i..j];
    ensures a[j..k] == b[j..k];
{
    if i == j { return; }
    SubSeqEQ(a,b,i+1,j,k);
    assert a[i] == b[i];
    assert a[i..j] == a[i..i+1]+a[i+1..j];
    assert b[i..j] == b[i..i+1]+b[i+1..j];
}

// Sanna að eins vendigildis quicksort skili raðaðri runu.
lemma QuicksortSorts<T>
        ( a0: seq<T>
        , a1: seq<T>
        , a2: seq<T>
        , a3: seq<T>
        , i: int
        , r: int
        , s: int
        , j: int
        , piv: T
        , comp: (T,T)->int
        )
    requires IsComparator(comp);
    requires 0 <= i <= r <= s <= j <= |a0| == |a1| == |a2| == |a3|;
    requires r <= s;
    requires a0[..i] == a1[..i];
    requires a0[j..] == a1[j..];
    requires multiset(a0[i..j]) == multiset(a1[i..j]);
    requires forall t | r <= t < s :: comp(a1[t],piv) == 0;
    requires forall t | i <= t < r :: comp(a1[t],piv) <= 0;
    requires forall t | s <= t < j :: comp(a1[t],piv) >= 0;
    requires a2[..i] == a1[..i];
    requires a2[r..] == a1[r..];
    requires multiset(a2[i..r]) == multiset(a1[i..r]);
    requires IsSorted(a2[i..r],comp);
    requires a3[..s] == a2[..s];
    requires a3[j..] ==a2[j..];
    requires multiset(a3[s..j]) == multiset(a2[s..j]);
    requires IsSorted(a3[s..j],comp);
    ensures a3[..i] == a0[..i];
    ensures a3[j..] == a0[j..];
    ensures IsSorted(a3[i..j],comp);
{
    // a0:  | ... |       ???       | ... |
    // a1:  | ... | <=p | ==p | >=p | ... |
    // a2:  | ... |  A  | ==p | >=p | ... |
    // a3   | ... |  A  | ==p |  C  | ... |
    //       0     i     r     s     j
    //
    ghost var A3 := a3[i..r];
    ghost var B3 := a3[r..s];
    ghost var C3 := a3[s..j];
    ghost var A2 := a2[i..r];
    ghost var B2 := a2[r..s];
    ghost var C2 := a2[s..j];
    ghost var A1 := a1[i..r];
    ghost var B1 := a1[r..s];
    ghost var C1 := a1[s..j];
    ghost var mA3 := multiset(A3);
    ghost var mA2 := multiset(A2);
    ghost var mA1 := multiset(A1);
    ghost var mB3 := multiset(B3);
    ghost var mB2 := multiset(B2);
    ghost var mB1 := multiset(B1);
    ghost var mC3 := multiset(C3);
    ghost var mC2 := multiset(C2);
    ghost var mC1 := multiset(C1);
    SubSeqEQ(a2,a3,0,i,r);
    assert A3 == A2;
    assert B3 == B2 == B1;
    assert C1 == C2;
    assert mA1 == mA2 == mA3;
    assert mB1 == mB2 == mB3;
    assert mC1 == mC2 == mC3;
    assert forall z :: z in A3 <==> z in mA3;
    assert forall z :: z in B3 <==> z in mB3;
    assert forall z :: z in C3 <==> z in mC3;
    assert forall z | z in A3 :: comp(z,piv) <= 0;
    assert forall z | z in B3 :: comp(z,piv) == 0;
    assert forall z | z in C3 :: comp(z,piv) >= 0;
    assert forall t | i <= t < r :: a3[t] in A3;
    assert forall t | r <= t < s :: a3[t] in B3;
    assert forall t | s <= t < j :: a3[t] in C3;
    assert forall p,q | i <= p < q < j ::
        (q < r) ||
        (p < r && r <= q < s) ||
        (p < r && s <= q) ||
        (r <= p < q < s) ||
        (r <= p < s <= q) ||
        (s <= p);
    assert forall p,q | i <= p < q < j ::
        (q < r && comp(a3[p],a3[q]) <= 0) ||
        (p < r && r <= q < s && comp(a3[p],a3[q]) <= 0) ||
        (p < r && s <= q && comp(a3[p],a3[q]) <= 0) ||
        (r <= p < q < s && comp(a3[p],a3[q]) <= 0) ||
        (r <= p < s <= q && comp(a3[p],a3[q]) <= 0) ||
        (s <= p && comp(a3[p],a3[q]) <= 0);
}

// Sanna að eins vendigildis quicksort skili runu sem er
// umröðun (permutation) af upphaflegu rununni.
lemma QuicksortPermutes<T>
        ( a0: seq<T>
        , a1: seq<T>
        , a2: seq<T>
        , a3: seq<T>
        , i: int
        , r: int
        , s: int
        , j: int
        , piv: T
        , comp: (T,T)->int
        )
    requires IsComparator(comp);
    requires 0 <= i <= r <= s <= j <= |a0| == |a1| == |a2| == |a3|;
    requires r <= s;
    requires a0[..i] == a1[..i];
    requires a0[j..] == a1[j..];
    requires multiset(a0[i..j]) == multiset(a1[i..j]);
    requires forall t | r <= t < s :: comp(a1[t],piv) == 0;
    requires forall t | i <= t < r :: comp(a1[t],piv) <= 0;
    requires forall t | s <= t < j :: comp(a1[t],piv) >= 0;
    requires a2[..i] == a1[..i];
    requires a2[r..] == a1[r..];
    requires multiset(a2[i..r]) == multiset(a1[i..r]);
    requires IsSorted(a2[i..r],comp);
    requires a3[..s] == a2[..s];
    requires a3[j..] ==a2[j..];
    requires multiset(a3[s..j]) == multiset(a2[s..j]);
    requires IsSorted(a3[s..j],comp);
    ensures a3[..i] == a0[..i];
    ensures a3[j..] == a0[j..];
    ensures multiset(a3[i..j]) == multiset(a0[i..j]);
{
    // a0:  | ... |       ???       | ... |
    // a1:  | ... | <=p | ==p | >=p | ... |
    // a2:  | ... |  A  | ==p | >=p | ... |
    // a3   | ... |  A  | ==p |  C  | ... |
    //       0     i     r     s     j
    //
    calc ==
    {
        multiset(a3[i..j]);
        assert a3[i..j] == a3[i..s]+a3[s..j];
        multiset(a3[i..s]+a3[s..j]);
        multiset(a3[i..s])+multiset(a3[s..j]);
        multiset(a3[i..s])+multiset(a2[s..j]);
        multiset(a2[i..s])+multiset(a2[s..j]);
        { SubSeqEQ(a1,a2,s,j,|a1|); }
        multiset(a2[i..s])+multiset(a1[s..j]);
        { SubSeqEQ(a1,a2,r,j,|a1|); }
        { SubSeqEQ(a1,a2,r,s,j); }
        assert a2[i..s] == a2[i..r]+a2[r..s];
        multiset(a2[i..r]+a2[r..s])+multiset(a1[s..j]);
        multiset(a2[i..r])+multiset(a2[r..s])+multiset(a1[s..j]);
        multiset(a1[i..r])+multiset(a2[r..s])+multiset(a1[s..j]);
        assert a2[r..s] == a1[r..s];
        multiset(a1[i..r])+multiset(a1[r..s])+multiset(a1[s..j]);
        multiset(a1[i..r]+a1[r..s])+multiset(a1[s..j]);
        assert a1[i..r]+a1[r..s] == a1[i..s];
        multiset(a1[i..s])+multiset(a1[s..j]);
        multiset(a1[i..s]+a1[s..j]);
        assert a1[i..s]+a1[s..j] == a1[i..j];
        multiset(a1[i..j]);
        multiset(a0[i..j]);
    }
}

// Sanna að samskeyting forskeytis og eftirskeytis skili
// upphaflegu rununni.
lemma Split<T>( a: seq<T>, i: int, j: int, k: int )
    requires 0 <= i <= j <= k <= |a|;
    ensures a[i..k] == a[i..j]+a[j..k];
{}

// Víxlar gildum í tveimur mismunandi sætum í fylki.
method Swap<T>( a: array<T>, i: int, j: int )
    modifies a;
    requires 0 <= i < j < a.Length;
    ensures a[..i] == old(a[..i]);
    ensures a[i+1..j] == old(a[i+1..j]);
    ensures a[j+1..] == old(a[j+1..]);
    ensures a[i] == old(a[j]);
    ensures a[j] == old(a[i]);
    ensures multiset(a[i..j]) == old(multiset(a[i+1..j+1]));
    ensures multiset(a[i+1..j+1]) == old(multiset(a[i..j]));
{
    a[i], a[j] := a[j], a[i];
    Split(a[..],i,i+1,j);
    calc ==
    {
        multiset(a[i..j]);
        multiset(a[i..i+1]+a[i+1..j]);
        multiset(a[i..i+1])+multiset(a[i+1..j]);
    }
}

// Sanna ýmsar einfaldar afleiðingar af víxlun gilda í fylki.
lemma SwappingLemma<T>( a: seq<T>, b: seq<T>, i: int, r: int, s: int, j: int )
    requires |a| == |b|;
    requires 0 <= i <= r < s < j <= |a|;
    requires a[..r] == b[..r];
    requires a[s+1..] == b[s+1..];
    requires a[r] == b[s];
    requires a[s] == b[r];
    requires a[r+1..s] == b[r+1..s];
    ensures multiset(a[i..j]) == multiset(b[i..j]);
    ensures b[..r] == a[..r];
    ensures b[s+1..] == a[s+1..];
    ensures b[r+1..s] == a[r+1..s];
    ensures b[r] == a[s];
    ensures b[s] == a[r];
    ensures multiset(a[i..j]) == multiset(b[i..j]);
    ensures b[..i] == a[..i];
    ensures b[j..] == a[j..];
{
    calc ==
    {
        a[i..j];
        a[i..r]+a[r..j];
        a[i..r]+a[r..r+1]+a[r+1..j];
        a[i..r]+a[r..r+1]+a[r+1..s]+a[s..j];
        a[i..r]+a[r..r+1]+a[r+1..s]+a[s..s+1]+a[s+1..j];
    }
    calc ==
    {
        b[i..j];
        b[i..r]+b[r..j];
        b[i..r]+b[r..r+1]+b[r+1..j];
        b[i..r]+b[r..r+1]+b[r+1..s]+b[s..j];
        b[i..r]+b[r..r+1]+b[r+1..s]+b[s..s+1]+b[s+1..j];
    }
    calc ==
    {
        multiset(a[i..j]);
        multiset(a[i..r]+a[r..r+1]+a[r+1..s]+a[s..s+1]+a[s+1..j]);
        multiset(a[i..r])+multiset(a[r..r+1])+multiset(a[r+1..s])+multiset(a[s..s+1])+multiset(a[s+1..j]);
        multiset(b[i..r])+multiset(a[r..r+1])+multiset(a[r+1..s])+multiset(a[s..s+1])+multiset(a[s+1..j]);
        multiset(b[i..r])+multiset(b[s..s+1])+multiset(a[r+1..s])+multiset(a[s..s+1])+multiset(a[s+1..j]);
        multiset(b[i..r])+multiset(b[s..s+1])+multiset(b[r+1..s])+multiset(a[s..s+1])+multiset(a[s+1..j]);
        multiset(b[i..r])+multiset(b[s..s+1])+multiset(b[r+1..s])+multiset(b[r..r+1])+multiset(a[s+1..j]);
        assert a[s+1..j] == b[s+1..j];
        multiset(b[i..r])+multiset(b[s..s+1])+multiset(b[r+1..s])+multiset(b[r..r+1])+multiset(b[s+1..j]);
        multiset(b[i..r])+multiset(b[r..r+1])+multiset(b[r+1..s])+multiset(b[s..s+1])+multiset(b[s+1..j]);
        multiset(b[i..r]+b[r..r+1]+b[r+1..s]+b[s..s+1]+b[s+1..j]);
        multiset(b[i..j]);
    }
}

// Sanna afleiðingar af víxlun sem eru gagnlegar í Lomuto flokkunarlykkju.
//
// a: |p| <p | >=p |x| ??? |
// b: |p| <p |x| >=p | ??? |
//     i      r     s       j
//
//   x<p
//
lemma SwappingLemmaLoop<T>( a: seq<T>, b: seq<T>, i: int, r: int, s: int, j: int, p: T, comp: (T,T)->int )
    requires |a| == |b|;
    requires 0 <= i < r < s < j <= |a|;
    requires a[..r] == b[..r];
    requires a[s+1..] == b[s+1..];
    requires a[r] == b[s];
    requires a[s] == b[r];
    requires a[r+1..s] == b[r+1..s];
    requires forall t | i < t < r :: comp(a[t],p) < 0;
    requires forall t | r <= t < s :: comp(a[t],p) >= 0;
    requires comp(a[s],p) < 0;
    requires a[i] == p;
    ensures a[i] == p;
    ensures multiset(a[i..j]) == multiset(b[i..j]);
    ensures b[..r] == a[..r];
    ensures b[s+1..] == a[s+1..];
    ensures b[r+1..s] == a[r+1..s];
    ensures b[r] == a[s];
    ensures b[s] == a[r];
    ensures multiset(a[i..j]) == multiset(b[i..j]);
    ensures b[..i] == a[..i];
    ensures b[j..] == a[j..];
    ensures forall t | i < t <= r :: comp(b[t],p) < 0;
    ensures forall t | r < t <= s :: comp(b[t],p) >= 0;
{
    SwappingLemma(a,b,i,r,s,j);
    assert forall t | r < t < s :: a[t] == b[t];
    assert comp(b[s],p) >= 0;
}

// Sanna afleiðingar af víxlun sem eru gagnlegar eftir að Lomuto flokkunarlykkju lýkur.
//
// a: |p| <p | >=p |
// b: | <p |p| >=p |
//     i    r       j
//
lemma SwappingLemmaFinal<T>( a: seq<T>, b: seq<T>, i: int, r: int, j: int, p: T, comp: (T,T)->int )
    requires |a| == |b|;
    requires 0 <= i < r < j <= |a|;
    requires a[..i] == b[..i];
    requires a[i+1..r] == b[i+1..r];
    requires a[r+1..] == b[r+1..];
    requires a[i] == b[r];
    requires a[r] == b[i];
    requires a[r+1..] == b[r+1..];
    requires forall t | i < t <= r :: comp(a[t],p) < 0;
    requires forall t | r < t < j :: comp(a[t],p) >= 0;
    requires comp(a[i],p) == 0;
    ensures multiset(a[i..j]) == multiset(b[i..j]);
    ensures multiset(a[i+1..r+1]) == multiset(b[i..r]);
    ensures b[..i] == a[..i];
    ensures b[r+1..] == a[r+1..];
    ensures b[i+1..r] == a[i+1..r];
    ensures b[r] == a[i];
    ensures b[i] == a[r];
    ensures multiset(a[i..j]) == multiset(b[i..j]);
    ensures b[..i] == a[..i];
    ensures b[j..] == a[j..];
    ensures forall t | i <= t < r :: comp(b[t],p) < 0;
    ensures forall t | r < t < j :: comp(b[t],p) >= 0;
    ensures comp(b[r],p) == 0;
{
    SwappingLemma(a,b,i,i,r,j);
    assert comp(b[i],p) < 0;
    assert forall t | i < t < r :: a[t] == b[t];
    assert forall t | i < t < r :: comp(b[t],p) < 0;
    calc ==
    {
        multiset(a[i+1..r+1]);
        assert a[i+1..r+1] == a[i+1..r]+a[r..r+1];
        multiset(a[i+1..r]+a[r..r+1]);
        multiset(a[i+1..r])+multiset(a[r..r+1]);
        multiset(b[i+1..r])+multiset(a[r..r+1]);
        multiset(b[i+1..r])+multiset(b[i..i+1]);
        multiset(b[i..i+1])+multiset(b[i+1..r]);
        multiset(b[i..i+1]+b[i+1..r]);
        assert b[i..r] == b[i..i+1]+b[i+1..r];
        multiset(b[i..r]);
    }
    assert multiset(a[i+1..r+1]) == multiset(b[i..r]);
}