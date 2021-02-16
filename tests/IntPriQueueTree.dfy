// Höfundur: Snorri Agnarsson, snorri@hi.is

include "IntPriQueue.dfy"
include "BST.dfy"

class IntPriQueueTree extends IntPriQueue
{
    var t: BST;
    
    predicate Valid()
        reads this, Repr;
    {
        ghostbag == multiset(TreeSeq(t)) &&
        TreeIsSorted(t) &&
        forall z | z in ghostbag :: z in TreeSeq(t)
    }

    constructor()
        ensures Valid() && fresh(Repr-{this});
        ensures |ghostbag| == 0;
    {
        new;
        Repr := {this};
        t := BSTEmpty;
        ghostbag := multiset(TreeSeq(t));
    }

    predicate method IsEmpty()
        reads this, Repr;
        requires Valid();
        ensures IsEmpty() <==> |ghostbag| == 0;
    {
        t == BSTEmpty
    }
    
    method Add( x: int )
        modifies this, Repr;
        requires Valid();
        ensures Valid() && fresh(Repr-old(Repr));
        ensures ghostbag == old(ghostbag)+multiset{x};
    {
        t := Insert(t,x);
        ghostbag := multiset(TreeSeq(t));
    }
    
    method RemoveMax() returns ( x: int )
        modifies this, Repr;
        requires Valid();
        requires |ghostbag| != 0;
        ensures Valid() && fresh(Repr-old(Repr));
        ensures x in old(ghostbag);
        ensures ghostbag == old(ghostbag)-multiset{x};
        ensures forall z | z in ghostbag :: x >= z;
    {
        t, x := DeleteMax(t);
        ghostbag := multiset(TreeSeq(t));
    }
}