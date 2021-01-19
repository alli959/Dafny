function pow( x: real, n: int ): real
    decreases n;
    requires n>=0;
    requires x != 0.0;
    ensures pow(x,n) != 0.0;
{
    if n == 0 then
        1.0
    else
        x*pow(x,n-1)
}

method Root ( f: real->real
            , a: real
            , b: real
            , eps: real
            , maxdepth: int
            )
        returns ( p: real, q: real )
    requires maxdepth >= 0;
    decreases maxdepth;
    requires a <= b;
    requires f(a)*f(b) <= 0.0;
    requires eps > 0.0;
    ensures a <= p <= q <= b;
    ensures q-p < eps || q-p == (b-a)/pow(2.0,maxdepth);
    ensures f(p)*f(q) <= 0.0;
{
    if maxdepth == 0 || b-a < eps { return a,b; }
    var m := (a+b)/2.0;
    if f(a)*f(m) <= 0.0 { p,q := Root(f,a,m,eps,maxdepth-1); }
    else                { p,q := Root(f,m,b,eps,maxdepth-1); }
}

method Show( x: real, n: int )
    requires n>=0;
{
    var z := x;
    if z < 0.0
    {
        print "-";
        z := -z;
    }
    var y := z.Floor;
    print y;
    z := z - (y as real);
    print ".";
    var i := 0;
    while i != n
        decreases n-i;
        invariant 0 <= i <= n;
    {
        z := 10.0*z;
        y := z.Floor;
        print y;
        z := z - (y as real);
        i := i+1;
    }
}

method Main()
{
    var eps := 0.0000000000000000000000000000000000000000000000000000001;
    Show(eps,80);
    print "\n";
    var a,b := Root(x=>2.0-x*x,1.4142135,1.4142136,eps,1000);
    print a;
    print "\n";
    print b;
    print "\n";
    Show(a,50);
    print "\n";
    Show(b,50);
    a := 1.41421355;
    a := (a+2.0/a)/2.0;
    a := (a+2.0/a)/2.0;
    a := (a+2.0/a)/2.0;
    a := (a+2.0/a)/2.0;
    print "\n";
    Show(a,80);
    a := (a+2.0/a)/2.0;
    print "\n";
    Show(a,80);
}