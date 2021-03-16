// Author: Snorri Agnarsson, snorri@hi.is

// An experiment with mutable lists.

// Dafny is barely able to verify this.
// The command line compiler accepts it
// on my computer, but Visual Studio
// Code does not finish the verification.

class Link
{
    var head: int;
    var tail: Link?;
}

class FiniteList
{
    ghost var linkseq: seq<Link>;
    ghost var intseq: seq<int>;
    var list: Link?;

    predicate Valid()
        reads this, this.list, linkseq;
    {
        IsSameChain(list,linkseq) &&
        |intseq| == |linkseq| &&
        (forall p,q | 0 <= p < q < |linkseq| :: linkseq[p] != linkseq[q]) &&
        ((list == null) <==> ((intseq == []) && (linkseq == []))) &&
        (forall i | 0 <= i < |intseq| :: intseq[i] == linkseq[i].head) &&
        (forall i | 0 < i < |intseq| :: linkseq[i-1].tail == linkseq[i]) &&
        (forall i | 0 <= i < |intseq|-1 :: linkseq[i].tail == linkseq[i+1]) &&
        (forall i | 0 <= i < |intseq| :: linkseq[i].tail == null ==> i == |intseq|-1) &&
        (linkseq != [] ==> linkseq[|linkseq|-1].tail == null) &&
        (list != null ==> linkseq != [] && linkseq[0] == list)
    }

    constructor( x: seq<int> )
        ensures Valid();
        ensures intseq == x;
        ensures fresh(linkseq);
    {
        list := null;
        linkseq := [];
        intseq := [];
        new;
        if x == [] { return; }
        var i := |x|;
        list := null;
        linkseq := [];
        intseq := [];
        while i != 0
            decreases i;
            invariant 0 <= i <= |x|;
            invariant |linkseq| == |x|-i;
            invariant fresh(linkseq);
            invariant intseq== x[i..];
            invariant Valid();
        {
            var tmp := new Link;
            i := i-1;
            tmp.head := x[i];
            tmp.tail := list;
            list := tmp;
            linkseq := [tmp]+linkseq;
            intseq := [x[i]]+intseq;
        }
    }

    method IntSeq() returns ( s: seq<int> )
        requires Valid();
        ensures s == intseq;
    {
        s := [];
        var nextLink := list;
        while nextLink != null
            decreases |intseq|-|s|;
            invariant 0 <= |s| <= |intseq|;
            invariant s == intseq[..|s|];
            invariant Valid();
            invariant linkseq == old(linkseq);
            invariant intseq == old(intseq);
            invariant forall r | 0 <= r < |linkseq| :: linkseq[r].head == old(linkseq[r].head);
            invariant forall r | 0 <= r < |linkseq| :: linkseq[r].tail == old(linkseq[r].tail);
            invariant nextLink != null ==> |s| < |linkseq| && nextLink == linkseq[|s|];
            invariant
                if |s| < |intseq| then
                    nextLink == linkseq[|s|]
                else
                    |s| == |linkseq| &&
                    nextLink == null;
        {
            s := s+[nextLink.head];
            nextLink := nextLink.tail;
        }
    }

    function Root(): Link?
        reads this, list, linkseq;
        requires Valid();
        ensures intseq == [] ==> Root() == null;
        ensures intseq != [] ==> Root() == list;
    {
        list
    }

    function method Head( c: Link ): int
        reads this, list, linkseq;
        requires Valid();
        requires c in linkseq;
        ensures list != null;
        ensures Head(c) == c.head;
    {
        c.head
    }

    method Tail( c: Link ) returns ( r: Link? )
        requires Valid();
        requires c in linkseq;
        ensures list != null;
        ensures r == c.tail;
        ensures r != null ==> r in linkseq;
    {
        ghost var idx :| 0 <= idx < |linkseq| && linkseq[idx] == c;
        r := c.tail;
        assert r != null ==> r == linkseq[idx+1];
    }

    method ShallowClone() returns ( r: FiniteList )
        requires Valid();
        ensures r.Valid();
        ensures r != this;
        ensures r.linkseq == linkseq;
    {
        r := new FiniteList([]);
        r.linkseq := linkseq;
        r.intseq := intseq;
        r.list := list;
    }

    method DeepClone() returns ( r: FiniteList )
        requires Valid();
        ensures r.Valid();
        ensures r != this;
        ensures r.intseq == intseq;
        ensures fresh(r.linkseq);
        ensures forall z | z in r.linkseq :: z !in linkseq;
    {
        var s := IntSeq();
        r := new FiniteList(s);
    }

    method ConsInt( x: int )
        requires Valid();
        modifies this;
        ensures Valid();
        ensures linkseq != [];
        ensures fresh(linkseq[0]);
        ensures intseq[0] == x;
        ensures linkseq[1..] == old(linkseq);
        ensures intseq[1..] == old(intseq);
    {
        var newLink := new Link;
        newLink.head := x;
        newLink.tail := list;
        list := newLink;
        linkseq := [newLink]+linkseq;
        intseq := [x]+intseq;
    }

    method ConsLink( x: Link )
        requires Valid();
        modifies this, x;
        requires x !in linkseq;
        ensures Valid();
        ensures linkseq == [x]+old(linkseq);
        ensures x.head == old(x.head);
        ensures intseq == [x.head]+old(intseq);
    {
        x.tail := list;
        list := x;
        linkseq := [x]+linkseq;
        intseq := [x.head]+intseq;
    }

    method RemoveHead() returns ( r: Link )
        requires Valid();
        modifies this;
        requires |linkseq| > 0;
        ensures Valid();
        ensures intseq == old(intseq[1..]);
        ensures linkseq == old(linkseq[1..]);
        ensures r == old(linkseq[0]);
        ensures r !in linkseq;
    {
        r := list;
        list := list.tail;
        assert forall p | 1 <= p < |linkseq| :: r != linkseq[p];
        linkseq := linkseq[1..];
        intseq := intseq[1..];
    }

    method ConstructiveReverse() returns ( r: FiniteList )
        requires Valid();
        ensures r.Valid();
        ensures fresh(r);
        ensures fresh(r.linkseq);
        ensures IsReverse(intseq,r.intseq);
    {
        r := new FiniteList([]);
        var rest := list;
        ghost var i := 0;
        while rest != null
            invariant 0 <= i <= |linkseq|;
            decreases |linkseq|-i;
            invariant r.Valid();
            invariant IsReverse(r.intseq,intseq[..i]);
            invariant fresh(r);
            invariant fresh(r.linkseq);
            invariant rest == null ==> i == |linkseq|;
            invariant rest != null ==> i < |linkseq| && rest == linkseq[i];
        {
            r.ConsInt(rest.head);
            assert i < |linkseq|-1 ==> rest.tail == linkseq[i+1];
            assert i == |linkseq|-1 ==> rest.tail == null;
            rest := rest.tail;
            i := i+1;
        }
    }

    method DestructiveReverse()
        requires Valid();
        modifies this, linkseq;
        ensures Valid();
        ensures IsReverse(intseq,old(intseq));
        ensures IsReverse(linkseq,old(linkseq));
    {
        if list == null { return; }
        if list.tail == null
        {
            assert list == linkseq[0];
            assert linkseq == [list];
            return;
        }
        var r := new FiniteList([]);
        ghost var i := 0;
        while list != null
            invariant 0 <= i <= old(|linkseq|);
            decreases old(|linkseq|)-i;
            invariant r.Valid();
            invariant Valid();
            invariant IsReverse(r.intseq,old(intseq[..i]));
            invariant IsReverse(r.linkseq,old(linkseq[..i]));
            invariant linkseq == old(linkseq[i..]);
            invariant intseq == old(intseq[i..]);
            invariant list == null ==> i == old(|linkseq|);
            invariant list != null ==> i < old(|linkseq|);
            invariant list != null ==> list == old(linkseq[i]);
            invariant forall z,w | z in linkseq && w in r.linkseq :: z != w;
            invariant i < old(|linkseq|) ==> list == old(linkseq[i]);
            invariant i == old(|linkseq|) ==> list == null;
        {
            assert list.head == old(intseq[i]);
            ghost var oldHead := list;
            ReverseStep(r.linkseq,old(linkseq[..i]),list);
            ReverseStep(r.intseq,old(intseq[..i]),list.head);
            assert list.head == old(intseq[i]);
            var linkToMove := RemoveHead();
            assert linkToMove !in linkseq;
            assert linkToMove !in r.linkseq;
            assert linkToMove.head == old(intseq[i]);
            assert linkToMove == oldHead;
            assert Valid();
            assert linkToMove == old(linkseq[i]);
            assert linkToMove !in linkseq;
            assert linkToMove.head == old(intseq[i]);
            assert Valid();
            r.ConsLink(linkToMove);
            assert linkToMove.head == old(intseq[i]);
            assert r.intseq[0] == old(intseq[i]);
            assert Valid();
            assert i < old(|linkseq|)-1 ==> list == old(linkseq[i+1]);
            assert i == old(|linkseq|)-1 ==> list == null;
            assert IsReverse(r.intseq[1..],old(intseq[..i]));
            i := i+1;
            assert IsReverse(r.intseq[1..],old(intseq[..i-1]));
            assert r.intseq[0] == old(intseq[i-1]);
            assert r.linkseq[0] == old(linkseq[i-1]);
            ReverseStep(r.intseq[1..],old(intseq[..i-1]),r.intseq[0]);
            ReverseStep(r.linkseq[1..],old(linkseq[..i-1]),r.linkseq[0]);
            assert IsReverse(r.intseq,old(intseq[..i]));
            assert IsReverse(r.linkseq,old(linkseq[..i]));
            assert forall z,w | z in linkseq && w in r.linkseq :: z != w;
        }
        list := r.list;
        intseq := r.intseq;
        linkseq := r.linkseq;
        assert IsReverse(intseq,old(intseq[..i]));
        assert IsReverse(linkseq,old(linkseq[..i]));
    }
}

predicate IsReverse<T>( a: seq<T>, b: seq<T> )
{
    |a| == |b| &&
    forall i | 0 <= i < |a| :: a[i] == b[|b|-i-1]
}

lemma ReverseStep<T>( a: seq<T>, b: seq<T>, x: T )
    decreases |a|;
    requires IsReverse(a,b);
    ensures IsReverse(a+[x],[x]+b);
    ensures IsReverse([x]+a,b+[x]);
{
    assert |a| == |b|;
    if a == [] { return; }
    ReverseStep(a[1..],b[..|a|-1],x);
    ReverseStep(a[..|a|-1],b[1..],x);
    assert a+[x] == a[..1]+a[1..]+[x];
    assert b+[x] == b[..1]+b[1..]+[x];
    assert a+[x] == a[..|a|-1]+a[|a|-1..]+[x];
    assert b+[x] == b[..|b|-1]+b[|b|-1..]+[x];
}

predicate IsSameChain( x: Link?, g: seq<Link> )
    decreases |g|;
    reads x,g;
{
    if x == null then
        g == []
    else if g == [] then
        false
    else
        |g| >= 1 &&
        x == g[0] &&
        ((x.tail == null) || (x.tail in g)) &&
        IsSameChain(x.tail,g[1..])
}