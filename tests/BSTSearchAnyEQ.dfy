include "BST.dfy"

method BSTSearchAnyEQ_Recursive( t: BST, x: int ) returns( r: BST, ghost p: seq<dir> )
    requires TreeIsSorted(t);
    ensures IsTreePath(t,p);
    ensures r == BSTEmpty <==> x !in TreeSeq(t);
    ensures r != BSTEmpty ==>
        IsTreePath(t,p) &&
        r == Subtree(t,p) &&
        RootValue(r) == x;
{
    if t == BSTEmpty
    {
        r := BSTEmpty;
        p := [];
        return;
    }
    if RootValue(t) == x
    {
        r := t;
        p := [];
        return;
    }
    TreePartitions(t,[]);
    if RootValue(t) < x
    {
        r,p := BSTSearchAnyEQ_Recursive(Right(t),x);
        p := [1]+p;
    }
    else
    {
        r,p := BSTSearchAnyEQ_Recursive(Left(t),x);
        p := [0]+p;
    }
}

method BSTSearchAnyEQ_Loop( t: BST, x: int ) returns( r: BST, ghost p: seq<dir> )
    requires TreeIsSorted(t);
    ensures IsTreePath(t,p);
    ensures r == BSTEmpty <==> x !in TreeSeq(t);
    ensures r != BSTEmpty ==>
        IsTreePath(t,p) &&
        r == Subtree(t,p) &&
        RootValue(r) == x;
{
    var s := t;
    var sp: seq<dir> := [];
    while s != BSTEmpty
        decreases s;
        invariant IsTreePath(t,sp);
        invariant s == Subtree(t,sp);
        invariant forall z | z in PreSeq(t,sp) :: z < x;
        invariant forall z | z in PostSeq(t,sp) :: z > x;
    {
        ExtendTreePath(t,sp);
        TreePartitions(t,sp);
        if RootValue(s) == x
        {
            r := s;
            p := sp;
            return;
        }
        if RootValue(s) < x
        {
            s := Right(s);
            sp := sp+[1];
            TreePartitions(t,sp);
        }
        else
        {
            s := Left(s);
            sp := sp+[0];
            TreePartitions(t,sp);
        }
    }
    TreePartitions(t,sp);
    p := [];
    r := BSTEmpty;
}