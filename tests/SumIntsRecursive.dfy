function sumInts( n: int ): int
    requires n >= 0;
    decreases n;
{
    if n == 0 then
        0
    else
        sumInts(n-1)+n
}

method SumIntsRecursive( n: int ) returns ( s: int )
    requires n >= 0;
    ensures s == sumInts(n)
    ensures s == n*(n+1)/2;
    decreases n;
{
    if n == 0 { return 0; }
    s := SumIntsRecursive(n-1);
    s := s+n;
}

method Main()
{
    var x := SumIntsRecursive(100);
    print x;

}