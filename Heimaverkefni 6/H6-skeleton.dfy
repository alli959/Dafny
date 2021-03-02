// Vistið þessa skrá með nafninu H6.java og klárið að
// forrita föllin SearchRecursive, SearchLoop og
// SearchTailRecursive.
// Í forrituninni skuluð þið fylgja þeim stöðulýsingum
// sem gefnar eru.

include "BST.dfy"

method SearchRecursive( t: BST, x: int )
        returns ( r1: BST
                , ghost r1p: seq<dir>
                , r2: BST
                , ghost r2p: seq<dir>
                )
    decreases t;
    requires TreeIsSorted(t);
    ensures r1 == BSTEmpty ==>
        forall z | z in TreeSeq(t) :: z > x;
    ensures r1 != BSTEmpty ==>
        IsTreePath(t,r1p) &&
        r1 == Subtree(t,r1p) &&
        (forall z | z in PreSeqIncluding(t,r1p) :: z <= x) &&
        (forall z | z in PostSeqExcluding(t,r1p) :: z > x);
    ensures r2 == BSTEmpty ==>
        forall z | z in TreeSeq(t) :: z <= x;
    ensures r2 != BSTEmpty ==>
        IsTreePath(t,r2p) &&
        r2 == Subtree(t,r2p) &&
        (forall z | z in PreSeqExcluding(t,r2p) :: z <= x) &&
        (forall z | z in PostSeqIncluding(t,r2p) :: z > x);
{
    RecursionSearchLemma();
    if t == BSTEmpty
    {
        ... hér vantar forritstexta
        return;
    }
    ExtendTreePath(t,[]);
    ... hér vantar forritstexta
}

method SearchLoop( t: BST, x: int )
        returns ( r1: BST
                , ghost r1p: seq<dir>
                , r2: BST
                , ghost r2p: seq<dir>
                )
    requires TreeIsSorted(t);
    ensures r1 == BSTEmpty ==>
        forall z | z in TreeSeq(t) :: z > x;
    ensures r1 != BSTEmpty ==>
        IsTreePath(t,r1p) &&
        r1 == Subtree(t,r1p) &&
        (forall z | z in PreSeqIncluding(t,r1p) :: z <= x) &&
        (forall z | z in PostSeqExcluding(t,r1p) :: z > x);
    ensures r2 == BSTEmpty ==>
        forall z | z in TreeSeq(t) :: z <= x;
    ensures r2 != BSTEmpty ==>
        IsTreePath(t,r2p) &&
        r2 == Subtree(t,r2p) &&
        (forall z | z in PreSeqExcluding(t,r2p) :: z <= x) &&
        (forall z | z in PostSeqIncluding(t,r2p) :: z > x);
{
    ... hér vantar forritstexta
    while s != BSTEmpty
        decreases s;
        invariant IsTreePath(t,sp);
        invariant s == Subtree(t,sp);
        invariant TreeIsSorted(s);
        invariant forall z | z in PreSeq(t,sp) :: z <= x;
        invariant forall z | z in PostSeq(t,sp) :: z > x;
        invariant r1 == BSTEmpty ==>
            PreSeq(t,sp) == [];
        invariant r1 != BSTEmpty ==>
            IsTreePath(t,r1p) &&
            r1 == Subtree(t,r1p) &&
            PreSeq(t,sp) != [] &&
            PostSeqExcluding(t,r1p) == TreeSeq(s)+PostSeq(t,sp) &&
            PreSeq(t,sp) == PreSeqIncluding(t,r1p) &&
            forall z | z in PreSeqIncluding(t,r1p) :: z <= x;
        invariant r2 == BSTEmpty ==>
            PostSeq(t,sp) == [];
        invariant r2 != BSTEmpty ==>
            IsTreePath(t,r2p) &&
            r2 == Subtree(t,r2p) &&
            PostSeq(t,sp) != [] &&
            PreSeqExcluding(t,r2p) == PreSeq(t,sp)+TreeSeq(s) &&
            PostSeq(t,sp) == PostSeqIncluding(t,r2p) &&
            forall z | z in PostSeqIncluding(t,r2p) :: z > x;
    {
        ExtendTreePath(t,sp);
        ... hér vantar forritstexta
        TreePartitions(t,sp);
    }
    if r1 != BSTEmpty { TreePartitions(t,r1p); }
    if r2 != BSTEmpty { TreePartitions(t,r2p); }
}

method {:tailrecursive true} SearchTailRecursive
                            ( ghost t: BST
                            , s: BST
                            , ghost sp: seq<dir>
                            , x: int
                            , c1: BST
                            , ghost c1p: seq<dir>
                            , c2: BST
                            , ghost c2p: seq<dir>
                            )
        returns ( r1: BST
                , ghost r1p: seq<dir>
                , r2: BST
                , ghost r2p: seq<dir>
                )
    decreases s;
    requires TreeIsSorted(t);
    requires TreeIsSorted(s);
    requires IsTreePath(t,sp);
    requires s == Subtree(t,sp);
    requires forall z | z in PreSeq(t,sp) :: z <= x;
    requires forall z | z in PostSeq(t,sp) :: z > x;
    requires c1 == BSTEmpty ==>
        PreSeq(t,sp) == [];
    requires c1 != BSTEmpty ==>
        PreSeq(t,sp) != [] &&
        IsTreePath(t,c1p) &&
        c1 == Subtree(t,c1p) &&
        PreSeq(t,sp) == PreSeqIncluding(t,c1p) &&
        PostSeqExcluding(t,c1p) == MidSeq(t,sp)+PostSeq(t,sp) &&
        forall z | z in PreSeqIncluding(t,c1p) :: z <= x;
    requires c2 == BSTEmpty ==>
        PostSeq(t,sp) == [];
    requires c2 != BSTEmpty ==>
        PostSeq(t,sp) != [] &&
        IsTreePath(t,c2p) &&
        c2 == Subtree(t,c2p) &&
        PostSeq(t,sp) == PostSeqIncluding(t,c2p) &&
        PreSeqExcluding(t,c2p) == PreSeq(t,sp)+MidSeq(t,sp) &&
        forall z | z in PostSeqIncluding(t,c2p) :: z > x;
    ensures r1 == BSTEmpty ==>
        forall z | z in TreeSeq(t) :: z > x;
    ensures r1 != BSTEmpty ==>
        IsTreePath(t,r1p) &&
        r1 == Subtree(t,r1p) &&
        (forall z | z in PreSeqIncluding(t,r1p) :: z <= x) &&
        (forall z | z in PostSeqExcluding(t,r1p) :: z > x);
    ensures r2 == BSTEmpty ==>
        forall z | z in TreeSeq(t) :: z <= x;
    ensures r2 != BSTEmpty ==>
        IsTreePath(t,r2p) &&
        r2 == Subtree(t,r2p) &&
        (forall z | z in PreSeqExcluding(t,r2p) :: z <= x) &&
        (forall z | z in PostSeqIncluding(t,r2p) :: z > x);
{
    if s == BSTEmpty
    {
        TreePartitions(t,sp);
        if c1 != BSTEmpty { TreePartitions(t,c1p); }
        if c2 != BSTEmpty { TreePartitions(t,c2p); }
        ... hér vantar forritstexta
        return;
    }
    ExtendTreePath(t,sp);
    ... hér vantar forritstexta
}

// Ef Dafny samþykkir Test fallið þá eru föllin að hegða sér rétt.
method Test( t: BST, x: int )
    requires TreeIsSorted(t);
{
    var r1,r2;
    ghost var p1,p2;
    r1,p1,r2,p2 := SearchRecursive(t,x);
    if r1 == BSTEmpty
    {
        assert forall z | z in TreeSeq(t) :: z > x;
    }
    else
    {
        assert IsTreePath(t,p1);
        assert Subtree(t,p1) == r1;
        assert forall z | z in PreSeqIncluding(t,p1) :: z <= x;
        assert forall z | z in PostSeqExcluding(t,p1) :: z > x;
    }
    if r2 == BSTEmpty
    {
        assert forall z | z in TreeSeq(t) :: z <= x;
    }
    else
    {
        assert IsTreePath(t,p2);
        assert Subtree(t,p2) == r2;
        assert forall z | z in PreSeqExcluding(t,p2) :: z <= x;
        assert forall z | z in PostSeqIncluding(t,p2) :: z > x;
    }
    r1,p1,r2,p2 := SearchLoop(t,x);
    if r1 == BSTEmpty
    {
        assert forall z | z in TreeSeq(t) :: z > x;
    }
    else
    {
        assert IsTreePath(t,p1);
        assert Subtree(t,p1) == r1;
        assert forall z | z in PreSeqIncluding(t,p1) :: z <= x;
        assert forall z | z in PostSeqExcluding(t,p1) :: z > x;
    }
    if r2 == BSTEmpty
    {
        assert forall z | z in TreeSeq(t) :: z <= x;
    }
    else
    {
        assert IsTreePath(t,p2);
        assert Subtree(t,p2) == r2;
        assert forall z | z in PreSeqExcluding(t,p2) :: z <= x;
        assert forall z | z in PostSeqIncluding(t,p2) :: z > x;
    }
    r1,p1,r2,p2 := SearchTailRecursive(t,t,[],x,BSTEmpty,[],BSTEmpty,[]);
    if r1 == BSTEmpty
    {
        assert forall z | z in TreeSeq(t) :: z > x;
    }
    else
    {
        assert IsTreePath(t,p1);
        assert Subtree(t,p1) == r1;
        assert forall z | z in PreSeqIncluding(t,p1) :: z <= x;
        assert forall z | z in PostSeqExcluding(t,p1) :: z > x;
    }
    if r2 == BSTEmpty
    {
        assert forall z | z in TreeSeq(t) :: z <= x;
    }
    else
    {
        assert IsTreePath(t,p2);
        assert Subtree(t,p2) == r2;
        assert forall z | z in PreSeqExcluding(t,p2) :: z <= x;
        assert forall z | z in PostSeqIncluding(t,p2) :: z > x;
    }
}
