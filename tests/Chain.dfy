// Höfundur: Snorri Agnarsson, snorri@hi.is

// Klasi fyrir eintengda lista breytanlegra hlekkja.
class Link<T>
{
    var head: T;
    var tail: Link?<T>;
    
    // x.Valid(chain) er satt þá og því aðeins
    // að x vísi á fremsta hlekk í keðju þeirra
    // hlekkja sem chain inniheldur. Aftasti
    // hlekkurinn í þeirri keðju verður að hafa
    // tail==null.
    predicate Valid( chain: seq<Link<T>> )
        reads this, chain;
        decreases chain;
    {
        if tail == null then
            chain == [this]
        else
            |chain| > 1 &&
            this == chain[0] &&
            tail == chain[1] &&
            tail.Valid(chain[1..]) &&
            chain[|chain|-1].tail == null &&
            forall i | 0 <= i < |chain|-1 :: chain[i].tail == chain[i+1]
    }
    
    // Smiðurinn gerir okkur kleift að skeyta nýjum hlekk
    // framan á löglega keðju, sem gefur þá lengri keðju.
    constructor( h: T, x: Link?<T>, ghost chain: seq<Link<T>> )
        requires (x == null && chain == []) || (x != null && x.Valid(chain));
        ensures Valid([this]+chain);    
        ensures head == h;
        ensures tail == x;
    {
        head := h;
        tail := x;
    }    
}

// ValueSeq(x) er runa gildanna sem hlekkirnir
// í x innihalda.
function ValueSeq<T>( x: seq<Link<T>> ): seq<T>
    reads x;
{
    if x == [] then [] else ValueSeq(x[..|x|-1])+[x[|x|-1].head]
}

// Append1 gerir okkur kleift að bæta hlekk aftan
// á keðju.
method Append1<T>( first: Link?<T>, ghost chain: seq<Link<T>>, last: Link?<T>, x: T )
        returns( newfirst: Link<T>, ghost newchain: seq<Link<T>>, newlast: Link<T> )
    modifies if chain == [] then [] else chain[|chain|-1..];
    requires first == null ==>
                chain == [] &&
                last == null;
    requires first != null ==>
                first.Valid(chain) &&
                last != null &&
                last == chain[|chain|-1] &&
                last.Valid([last]);
    ensures fresh(newlast);
    ensures newlast.Valid([newlast]);
    ensures newchain == chain+[newlast];
    ensures newfirst.Valid(newchain);
    ensures newlast.head == x;
    ensures ValueSeq(chain) == old(ValueSeq(chain));
    ensures ValueSeq(newchain) == ValueSeq(chain)+[x];
{
    newlast := new Link<T>(x,null,[]);
    if last == null
    {
        newfirst := newlast;
        newchain := [newlast];
        return;
    }
    newfirst := first;
    last.tail := newlast;
    newchain := chain+[newlast];
}

method Prepend1<T>( first: Link?<T>, ghost chain: seq<Link<T>>, last: Link?<T>, x: T )
        returns( newfirst: Link<T>, ghost newchain: seq<Link<T>>, newlast: Link<T> )
    requires first == null ==>
                chain == [] &&
                last == null;
    requires first != null ==>
                first.Valid(chain) &&
                last != null &&
                last == chain[|chain|-1] &&
                last.Valid([last]);
    ensures fresh(newfirst);
    ensures newlast.Valid([newlast]);
    ensures newchain == [newfirst]+chain;
    ensures newfirst.Valid(newchain);
    ensures newfirst.head == x;
    ensures ValueSeq(chain) == old(ValueSeq(chain));
    ensures ValueSeq(newchain) == [x]+ValueSeq(chain);
{
    newfirst := new Link(x,first,chain);
    if first == null
    {
        newlast := newfirst;
    }
    else
    {
        newlast := last;
    }
    newchain := [newfirst]+chain;
    ConcatValueSeq([newfirst],chain);
}

// Augljós sannindi um samskeytingar hlekkjaruna.
lemma ConcatValueSeq<T>( x: seq<Link<T>>, y: seq<Link<T>> )
    decreases y;
    ensures ValueSeq(x+y) == ValueSeq(x)+ValueSeq(y);
{
    if |y| == 0
    {
        assert x+y == x;
        return;
    }
    ConcatValueSeq(x,y[..|y|-1]);
    assert y == y[..|y|-1]+[y[|y|-1]];
    assert x+y == x+y[..|y|-1]+[y[|y|-1]];
}

// Augljós sannindi um hlekkjarunur og
// samsvarandi gildarunur.
lemma TailSeqLemma<T>( x: seq<Link<T>> )
    ensures |ValueSeq(x)| == |x|;
    ensures forall i | 0 <= i < |x| :: ValueSeq(x)[i] == x[i].head;
{
    if |x| == 0 { return; }
    TailSeqLemma(x[..|x|-1]);
    assert x[|x|-1].head == ValueSeq(x)[|x|-1];
}

// Ýmis gagnleg sannindi um hlekkjarunur og
// samsvarandi gildarunur.
lemma ValueSeqLemma<T>( x: seq<Link<T>>, y: seq<T> )
    requires |x| != 0;
    requires y == ValueSeq(x);
    ensures |x| == |y|;
    ensures x[0].head == y[0];
    ensures y == ValueSeq(x[..1])+ValueSeq(x[1..]);
    ensures x == x[..1]+x[1..];
    ensures y == y[..1]+y[1..];
    ensures ValueSeq(x[1..]) == y[1..];
    ensures |x| == |y|;
{
    TailSeqLemma(x);
    if |x| == 1 { return; }
    TailSeqLemma(x[..1]);
    TailSeqLemma(x[1..]);
    ValueSeqLemma(x[..|x|-1],y[..|x|-1]);
    assert x == x[..1]+x[1..];
    assert x == x[..|x|-1]+x[|x|-1..];
    assert |y| == |x|;
    assert y == y[..1]+y[1..];
    assert y == y[..|x|-1]+y[|x|-1..];
}
