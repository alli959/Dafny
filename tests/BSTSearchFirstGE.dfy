include "BST.dfy"

method BSTSearchFirstGE_Recursive( t: BST, x: int ) returns( r: BST, ghost p: seq<dir> )
    requires TreeIsSorted(t);
    ensures IsTreePath(t,p);
    ensures r == Subtree(t,p);
    ensures r == BSTEmpty ==> forall z | z in TreeSeq(t) :: z < x;
    ensures r != BSTEmpty ==> forall z | z in PreSeqExcluding(t,p) :: z < x;
    ensures r != BSTEmpty ==> forall z | z in PostSeqIncluding(t,p) :: z >= x;
{
    RecursionSearchLemma();
    if t == BSTEmpty
    {
        r := BSTEmpty;
        p := [];
    }
    else if RootValue(t) < x
    {
        r,p := BSTSearchFirstGE_Recursive(Right(t),x);
        p := [1]+p;
    }
    else
    {
        r,p := BSTSearchFirstGE_Recursive(Left(t),x);
        if r == BSTEmpty
        {
            p := [];
            r := t;
        }
        else
        {
            p := [0]+p;
        }
    }
}

method BSTSearchFirstGE_Loop( t: BST, x: int ) returns( r: BST, ghost rp: seq<dir> )
    requires TreeIsSorted(t);
    ensures (forall z | z in TreeSeq(t) :: z < x) <==> r == BSTEmpty;
    ensures r != BSTEmpty ==>
        IsTreePath(t,rp) &&
        r == Subtree(t,rp) &&
        (forall z | z in PreSeqExcluding(t,rp) :: z < x) &&
        (forall z | z in PostSeqIncluding(t,rp) :: z >= x);
{
    r := BSTEmpty;
    var sp := [];
    rp := [];
    var s := t;
    while s != BSTEmpty
        // | PreSeq(t,sp) | MidSeq(t,sp) |     PostSeq(t,sp)      |
        // |              |  TreeSeq(s)  |                        |
        // |   PreSeqExcluding(t,rp)     | PostSeqIncluding(t,rp) |
        // |      <x      |     ???      |           >=x          |
        //                                ^
        //                                r (ef ekki tómt)
        decreases s;
        invariant IsTreePath(t,sp);
        invariant IsTreePath(t,rp);
        invariant s == Subtree(t,sp);
        invariant TreeIsSorted(s);
        invariant forall z | z in PostSeq(t,sp) :: z >= x;
        invariant forall z | z in PreSeq(t,sp) :: z < x;
        invariant r == BSTEmpty <==> PostSeq(t,sp) == []
        invariant r != BSTEmpty ==>
            r == Subtree(t,rp) &&
            PreSeqExcluding(t,rp) == PreSeq(t,sp)+TreeSeq(s) &&
            PostSeqIncluding(t,rp) == PostSeq(t,sp);
    {
        ExtendTreePath(t,sp);
        if RootValue(s) >= x
        {
            rp := sp;
            r := s;
            sp := sp+[0];
            s := Left(s);
        }
        else
        {
            sp := sp+[1];
            s := Right(s);
        }
    }
    TreePartitions(t,sp);
    TreePartitions(t,rp);
}

method BSTSearchAnyEQ_Recursive( t: BST, x: int ) returns( r: BST, ghost p: seq<dir> )
    requires TreeIsSorted(t);
    ensures IsTreePath(t,p);
    ensures r == Subtree(t,p);
    ensures r == BSTEmpty <==> x !in TreeSeq(t);
    ensures r != BSTEmpty ==> RootValue(r) == x;
{
    if t == BSTEmpty
    {
        r := BSTEmpty;
        p := [];
    }
    else if RootValue(t) == x
    {
        r := t;
        p := [];
    }
    else if RootValue(t) < x
    {
        assert x !in TreeSeq(Left(t));
        r,p := BSTSearchAnyEQ_Recursive(Right(t),x);
        p := [1]+p;
    }
    else
    {
        assert x !in TreeSeq(Right(t));
        r,p := BSTSearchAnyEQ_Recursive(Left(t),x);
        p := [0]+p;
    }
}