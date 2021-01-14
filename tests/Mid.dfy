method Mid( p: int, q: int) returns ( m: int )
    // | ... | ??? | ... |
    //        p m   q
    requires p <= q;
    ensures p<= m <= q;
    ensures m-p <= q-m;
    ensures 0 <= (q-m)-(m-p) <= 1;

{
    m := (p+q)/2;
    assert m == p+(q-p)/2;
}


method Main() 
{
    var x := Mid(40, 100);
    print x;
}